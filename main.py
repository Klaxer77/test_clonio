# server.py (FULL) — FIX + OPT: smooth growth (float length) + cache per-tick state items + cache foods per-cell + throttle seg_grid rebuild
from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse
import asyncio, random, time, logging, math
from collections import deque, defaultdict
from typing import Dict, Tuple, Set, Optional, List, Deque

import orjson

logging.basicConfig(level=logging.INFO)
app = FastAPI()

WORLD_W = 3000
WORLD_H = 3000
SEGMENT = 30
TICK = 0.025  # 40 Hz

FOOD_COUNT = 500
FOOD_RESPAWN = 1.5
GROW_AMOUNT = 0.02

SPEED = 7
SPAWN_PROTECTION = 0

BOOST_MULT = 1.8
BOOST_MIN_LEN = 6
BOOST_COST_PER_TICK = 0.14

# максимум, сколько можно списать за тик, чтобы не было резких скачков
BOOST_MAX_COST_PER_TICK = 0.35
BOOST_FOOD_SIZE = 1.2

SEG_DIST = SEGMENT * 0.85

DROP_FOOD_CAP = 500
TOTAL_FOOD_CAP = FOOD_COUNT + DROP_FOOD_CAP

DROP_GROW = 1

# FIX: grow is smooth, so tick growth is fractional
MAX_GROW_PER_TICK = 0.25  # 0.15..0.4

PATH_MAX_STEP = SEG_DIST * 1.4

CORPSE_FOOD_SIZE = 1.7
CORPSE_JITTER = 0.0
CORPSE_MAX_PER_DEATH = 450
CORPSE_SPACING = SEGMENT * 0.85

HIT_RADIUS = SEGMENT * 0.95 * 1.35

IGNORE_OTHER_HEAD_SEGS = 1
IGNORE_OTHER_TAIL_SEGS = 0
TAIL_RADIUS_SCALE = 1.25

EAT_RADIUS = SEGMENT * 0.70

# ширина “хвата” (вбок)
EAT_SIDE_MULT = 2.0   # 1.3..2.2
EAT_FWD_MULT  = 1.0   # по длине не меняем

DEATH_SNAPSHOT_DELAY = 0.55
DEATH_AFTER_DELAY    = 0.08

GRID_CELL = int(SEGMENT * 10)

MAX_LEN = 450
FOODS_SEND_EVERY = 4
FOOD_VIEW_CELLS = 8

START_LEN = 10

STATE_SEND_HZ = 20
STATE_SEND_EVERY_TICKS = max(1, int(round((1.0 / STATE_SEND_HZ) / TICK)))
PATH_SEND_LAST_N = 24

# keyframe less often
KEYFRAME_EVERY_TICKS = 40 * 6  # ~6 sec
# do not include huge "body" in keyframe for long snakes
MAX_KEYFRAME_LEN = 260

AOI_CELLS = 3

SEND_QUEUE_MAX = 2
send_queues: Dict[str, Dict[str, asyncio.Queue]] = defaultdict(dict)
send_workers: Dict[str, Dict[str, asyncio.Task]] = defaultdict(dict)

SEG_GRID_CELL = int(SEGMENT * 4)
SEG_NEIGHBOR_CELLS = 2

# OPT: rebuild seg_grid not every tick
SEG_GRID_EVERY_TICKS = 2

rooms: Dict[str, Dict[str, dict]] = {}
connections: Dict[str, Dict[str, WebSocket]] = {}
foods: Dict[str, list] = {}

food_grid: Dict[str, Dict[Tuple[int, int], Set[int]]] = {}
player_grid: Dict[str, Dict[Tuple[int, int], Set[str]]] = {}
food_dirty: Dict[str, bool] = defaultdict(bool)
room_tick: Dict[str, int] = defaultdict(int)

base_food_debt: Dict[str, int] = defaultdict(int)
base_food_task: Dict[str, asyncio.Task] = {}

death_tasks: Set[asyncio.Task] = set()

seg_grid: Dict[str, Dict[Tuple[int, int], List[Tuple[str, int]]]] = defaultdict(lambda: defaultdict(list))


def cell_of_xy(x: float, y: float) -> Tuple[int, int]:
    return int(x // GRID_CELL), int(y // GRID_CELL)

def seg_cell_of_xy(x: float, y: float) -> Tuple[int, int]:
    return int(x // SEG_GRID_CELL), int(y // SEG_GRID_CELL)

def random_food(size: float = 1.0, kind: str = "base"):
    return {
        "x": random.randint(0, WORLD_W // SEGMENT - 1) * SEGMENT,
        "y": random.randint(0, WORLD_H // SEGMENT - 1) * SEGMENT,
        "color": f"hsl({random.randint(0,360)},80%,60%)",
        "size": float(size),
        "kind": kind,
    }

def count_kind(room_id: str, kind: str) -> int:
    return sum(1 for f in foods.get(room_id, []) if f.get("kind") == kind)

def rebuild_food_grid(room_id: str):
    g: Dict[Tuple[int, int], Set[int]] = defaultdict(set)
    arr = foods.get(room_id, [])
    for i, f in enumerate(arr):
        cx, cy = cell_of_xy(f["x"], f["y"])
        g[(cx, cy)].add(i)
    food_grid[room_id] = g

def rebuild_player_grid(room_id: str):
    g: Dict[Tuple[int, int], Set[str]] = defaultdict(set)
    pl = rooms.get(room_id, {})
    for pid, p in pl.items():
        h = p.get("head")
        if not h:
            continue
        cx, cy = cell_of_xy(h["x"], h["y"])
        g[(cx, cy)].add(pid)
    player_grid[room_id] = g

def ensure_base_food_worker(room_id: str):
    if base_food_debt[room_id] <= 0:
        return
    t = base_food_task.get(room_id)
    if t is None or t.done():
        base_food_task[room_id] = asyncio.create_task(base_food_worker(room_id))

async def base_food_worker(room_id: str):
    while True:
        if room_id not in foods:
            return
        if base_food_debt[room_id] <= 0:
            return

        await asyncio.sleep(FOOD_RESPAWN)

        if room_id not in foods:
            return
        if base_food_debt[room_id] <= 0:
            return

        base_now = count_kind(room_id, "base")
        need = max(0, FOOD_COUNT - base_now)
        if need <= 0:
            base_food_debt[room_id] = 0
            return

        can_add = min(
            base_food_debt[room_id],
            need,
            max(1, FOOD_COUNT // 25),
        )

        if len(foods[room_id]) >= TOTAL_FOOD_CAP:
            continue

        for _ in range(can_add):
            if len(foods[room_id]) >= TOTAL_FOOD_CAP:
                break
            foods[room_id].append(random_food(1.0, "base"))
            base_food_debt[room_id] -= 1

        food_dirty[room_id] = True

def normalize_dir_unit(d: dict) -> dict:
    try:
        x = float(d.get("x", 0))
        y = float(d.get("y", 0))
    except Exception:
        return {"x": 1.0, "y": 0.0}

    l = math.hypot(x, y)
    if l == 0:
        return {"x": 1.0, "y": 0.0}
    return {"x": x / l, "y": y / l}

def food_growth(food: dict) -> float:
    g = food.get("grow", None)
    if g is not None:
        try:
            return max(0.0, float(g))
        except Exception:
            return 0.0

    kind = food.get("kind", "base")
    if kind == "drop":
        return float(DROP_GROW)

    try:
        size = float(food.get("size", 1.0))
    except Exception:
        size = 1.0
    size = max(0.25, min(size, 5.0))

    return float(max(1, int(round(GROW_AMOUNT * size))))

def can_eat(head_x: float, head_y: float, food: dict, u: dict) -> bool:
    hx = float(head_x) + SEGMENT * 0.5
    hy = float(head_y) + SEGMENT * 0.5
    fx = float(food["x"]) + SEGMENT * 0.5
    fy = float(food["y"]) + SEGMENT * 0.5

    dx = fx - hx
    dy = fy - hy

    ux = float(u.get("x", 1.0))
    uy = float(u.get("y", 0.0))
    ul = math.hypot(ux, uy)
    if ul < 1e-9:
        ux, uy = 1.0, 0.0
    else:
        ux, uy = ux / ul, uy / ul

    lx, ly = -uy, ux

    fwd  = dx * ux + dy * uy
    side = dx * lx + dy * ly

    a = EAT_RADIUS * EAT_FWD_MULT
    b = EAT_RADIUS * EAT_SIDE_MULT

    # Проверка на то, что еда находится в пределах изменённого радиуса
    return (fwd * fwd) / (a * a) + (side * side) / (b * b) <= 1.0


def collect_food_near(room_id: str, x: float, y: float) -> List[dict]:
    cx, cy = cell_of_xy(x, y)
    g = food_grid.get(room_id) or {}
    arr = foods.get(room_id, [])
    out: List[dict] = []
    for dx in range(-FOOD_VIEW_CELLS, FOOD_VIEW_CELLS + 1):
        for dy in range(-FOOD_VIEW_CELLS, FOOD_VIEW_CELLS + 1):
            for idx in g.get((cx + dx, cy + dy), ()):
                if 0 <= idx < len(arr):
                    out.append(arr[idx])
    return out

def _clamp(v: float, a: float, b: float) -> float:
    return a if v < a else b if v > b else v

def dist2_point_to_segment(px, py, ax, ay, bx, by) -> float:
    abx = bx - ax
    aby = by - ay
    apx = px - ax
    apy = py - ay
    ab2 = abx * abx + aby * aby
    if ab2 <= 1e-9:
        dx = px - ax
        dy = py - ay
        return dx * dx + dy * dy
    t = (apx * abx + apy * aby) / ab2
    t = _clamp(t, 0.0, 1.0)
    cx = ax + abx * t
    cy = ay + aby * t
    dx = px - cx
    dy = py - cy
    return dx * dx + dy * dy

def _append_path_node(path: Deque[dict], v: int, x: float, y: float) -> float:
    if not path:
        path.appendleft({"x": x, "y": y, "ds": 0.0, "v": v})
        return 0.0

    hx = path[0]["x"]
    hy = path[0]["y"]
    ds = math.hypot(x - hx, y - hy)
    if ds < 1e-6:
        return 0.0

    path.appendleft({"x": x, "y": y, "ds": ds, "v": v})
    return ds

def append_head_point_dense(path: Deque[dict], v: int, x: float, y: float, max_step: float = PATH_MAX_STEP) -> float:
    if not path:
        path.appendleft({"x": x, "y": y, "ds": 0.0, "v": v})
        return 0.0

    hx = path[0]["x"]
    hy = path[0]["y"]
    dx = x - hx
    dy = y - hy
    d = math.hypot(dx, dy)
    if d < 1e-6:
        return 0.0

    if d <= max_step:
        return _append_path_node(path, v, x, y)

    added = 0.0
    steps = max(2, int(math.ceil(d / max_step)))
    for k in range(1, steps + 1):
        t = k / steps
        added += _append_path_node(path, v, hx + dx * t, hy + dy * t)
    return added

def trim_path_fast(path: Deque[dict], p: dict, need_len: float):
    while len(path) > 2 and float(p.get("path_len", 0.0)) > need_len:
        last = path.pop()
        p["path_len"] = float(p.get("path_len", 0.0)) - float(last.get("ds", 0.0))
        if p["path_len"] < 0:
            p["path_len"] = 0.0

# FIX: smooth tail by using float length and placing last point exactly at tail distance
def build_snake_flat_from_path(path: Deque[dict], length_units: float) -> list:
    lu = float(length_units)
    if lu < 1.0:
        lu = 1.0

    if not path:
        return [0.0, 0.0]

    tail_dist = max(0.0, (lu - 1.0) * SEG_DIST)
    n_points = max(1, int(math.floor(tail_dist / SEG_DIST)) + 2)

    out: List[float] = []

    a0 = path[0]
    out.extend([float(a0["x"]), float(a0["y"])])
    if n_points == 1:
        return out

    acc = 0.0
    next_mark = SEG_DIST

    ax, ay = float(a0["x"]), float(a0["y"])

    for i in range(len(path) - 1):
        b = path[i + 1]
        bx, by = float(b["x"]), float(b["y"])
        seg_len = float(b.get("ds", 0.0))
        if seg_len <= 1e-6:
            ax, ay = bx, by
            continue

        while next_mark <= (acc + seg_len) + 1e-6:
            t = (next_mark - acc) / seg_len
            x = ax + (bx - ax) * t
            y = ay + (by - ay) * t
            out.extend([x, y])

            if next_mark >= tail_dist - 1e-6:
                return out

            next_mark += SEG_DIST
            if next_mark > tail_dist:
                next_mark = tail_dist

        acc += seg_len
        ax, ay = bx, by

    lx, ly = float(path[-1]["x"]), float(path[-1]["y"])
    while (len(out) // 2) < n_points:
        out.extend([lx, ly])

    return out

def spawn_corpse_food(room_id: str, p: dict):
    if room_id not in foods:
        return

    body_flat = p.get("snake") or []
    if len(body_flat) < 4:
        return

    pts = []
    for i in range(0, len(body_flat), 2):
        pts.append((float(body_flat[i]), float(body_flat[i + 1])))
    if len(pts) < 2:
        return

    arr = foods[room_id]
    free = max(0, TOTAL_FOOD_CAP - len(arr))
    if free <= 0:
        return

    spacing = float(CORPSE_SPACING)
    sampled: List[Tuple[float, float]] = []
    used = set()

    def push_xy(x: float, y: float):
        gx = int(round(x / SEGMENT)) * SEGMENT
        gy = int(round(y / SEGMENT)) * SEGMENT
        gx = max(0, min(gx, WORLD_W - SEGMENT))
        gy = max(0, min(gy, WORLD_H - SEGMENT))
        key = (gx, gy)
        if key in used:
            return
        used.add(key)
        sampled.append((float(gx), float(gy)))

    push_xy(pts[0][0], pts[0][1])

    carry = 0.0
    for i in range(len(pts) - 1):
        ax, ay = pts[i]
        bx, by = pts[i + 1]
        dx = bx - ax
        dy = by - ay
        seg_len = math.hypot(dx, dy)
        if seg_len < 1e-6:
            continue

        ux = dx / seg_len
        uy = dy / seg_len

        t = spacing - carry
        if t < 0.0:
            t = 0.0

        while t <= seg_len + 1e-6:
            x = ax + ux * t
            y = ay + uy * t
            push_xy(x, y)
            t += spacing

        carry = (carry + seg_len) % spacing

    spawn_cap = min(len(sampled), int(free), int(CORPSE_MAX_PER_DEATH))
    if spawn_cap <= 0:
        return
    sampled = sampled[:spawn_cap]

    color = p.get("color")
    dead_len = float(p.get("length", 0.0))
    need_total = max(0.0, dead_len - float(START_LEN))

    m = len(sampled)
    if m <= 0:
        return

    base_grow = need_total / float(m)

    for (x, y) in sampled:
        if len(arr) >= TOTAL_FOOD_CAP:
            break

        if CORPSE_JITTER:
            x += random.uniform(-CORPSE_JITTER, CORPSE_JITTER)
            y += random.uniform(-CORPSE_JITTER, CORPSE_JITTER)

        arr.append({
            "x": x,
            "y": y,
            "color": color,
            "size": float(CORPSE_FOOD_SIZE),
            "kind": "corpse",
            "grow": float(base_grow),
        })

    food_dirty[room_id] = True


@app.get("/")
async def index():
    with open("index.html", encoding="utf-8") as f:
        return HTMLResponse(f.read())

def dumps_bytes(payload: dict) -> bytes:
    return orjson.dumps(payload, option=orjson.OPT_NON_STR_KEYS)

async def send_worker(ws: WebSocket, q: asyncio.Queue):
    while True:
        b = await q.get()
        try:
            await ws.send_bytes(b)
        except Exception:
            return

async def enqueue_send(room_id: str, pid: str, payload: dict):
    q = send_queues.get(room_id, {}).get(pid)
    if not q:
        return
    if q.full():
        try:
            q.get_nowait()
        except Exception:
            pass
    try:
        q.put_nowait(dumps_bytes(payload))
    except Exception:
        pass

async def death_flow(room_id: str, pid: str, ws: WebSocket, last_payload: dict):
    try:
        await ws.send_bytes(dumps_bytes(last_payload))
        await asyncio.sleep(DEATH_SNAPSHOT_DELAY)
        await ws.send_bytes(dumps_bytes({"type": "death"}))
        await asyncio.sleep(DEATH_AFTER_DELAY)
        await ws.close()
    except Exception:
        pass
    finally:
        send_queues.get(room_id, {}).pop(pid, None)
        t = send_workers.get(room_id, {}).pop(pid, None)
        if t and not t.done():
            t.cancel()

@app.websocket("/ws/{room_id}/{player_id}")
async def ws_handler(ws: WebSocket, room_id: str, player_id: str):
    await ws.accept()
    logging.info(f"[{player_id}] Connected to room {room_id}")

    if room_id not in rooms:
        rooms[room_id] = {}
        connections[room_id] = {}
        foods[room_id] = [random_food(1.0, "base") for _ in range(FOOD_COUNT)]
        rebuild_food_grid(room_id)
        rebuild_player_grid(room_id)
        base_food_debt[room_id] = 0

    x = random.randint(8, (WORLD_W // SEGMENT) - 8) * SEGMENT
    y = random.randint(8, (WORLD_H // SEGMENT) - 8) * SEGMENT

    path: Deque[dict] = deque()
    path_ver = 1
    path.appendleft({"x": float(x), "y": float(y), "ds": 0.0, "v": path_ver})
    init_path_len = 0.0

    for i in range(1, 14):
        px = float(x - i * (SEG_DIST * 0.9))
        py = float(y)
        prev = path[-1]
        ds = math.hypot(px - prev["x"], py - prev["y"])
        path.append({"x": px, "y": py, "ds": ds, "v": path_ver})
        init_path_len += ds

    rooms[room_id][player_id] = {
        "boost_spent": 0.0,
        "dir": {"x": 1.0, "y": 0.0},
        "color": f"hsl({random.randint(0,360)},80%,50%)",
        "spawn_time": time.time(),
        "boost": False,
        "tick_i": 0,

        "path": path,
        "path_len": float(init_path_len),
        "path_ver": path_ver,

        "head": {"x": float(x), "y": float(y)},
        "length": float(START_LEN),
        "pending_grow": 0.0,

        "snake": [],

        "cell": cell_of_xy(x, y),
        "seg_cell": seg_cell_of_xy(x, y),
    }

    connections[room_id][player_id] = ws

    q = asyncio.Queue(maxsize=SEND_QUEUE_MAX)
    send_queues[room_id][player_id] = q
    send_workers[room_id][player_id] = asyncio.create_task(send_worker(ws, q))

    rebuild_player_grid(room_id)

    try:
        while True:
            data = await ws.receive_json()
            p = rooms[room_id].get(player_id)
            if not p:
                continue

            if data.get("type") == "ping":
                await ws.send_bytes(dumps_bytes({"type": "pong", "t": data.get("t", 0)}))
                continue

            if "direction" in data:
                new_u = normalize_dir_unit(data["direction"])
                old_u = p["dir"]
                dot = old_u["x"] * new_u["x"] + old_u["y"] * new_u["y"]
                if dot > -0.98:
                    p["dir"] = new_u

            if "boost" in data:
                p["boost"] = bool(data["boost"])

    except WebSocketDisconnect:
        logging.info(f"[{player_id}] Disconnected")
    except Exception as e:
        logging.info(f"[{player_id}] Error: {e}")
    finally:
        rooms[room_id].pop(player_id, None)
        connections[room_id].pop(player_id, None)
        rebuild_player_grid(room_id)

        send_queues.get(room_id, {}).pop(player_id, None)
        t = send_workers.get(room_id, {}).pop(player_id, None)
        if t and not t.done():
            t.cancel()

def iter_neighbor_food_indices(room_id: str, cx: int, cy: int):
    g = food_grid.get(room_id) or {}
    for dx in range(-1, 2):
        for dy in range(-1, 2):
            for idx in g.get((cx + dx, cy + dy), ()):
                yield idx

def collect_players_near(room_id: str, cx: int, cy: int) -> List[str]:
    g = player_grid.get(room_id) or {}
    out: List[str] = []
    for dx in range(-AOI_CELLS, AOI_CELLS + 1):
        for dy in range(-AOI_CELLS, AOI_CELLS + 1):
            out.extend(list(g.get((cx + dx, cy + dy), ())))
    return out

def rebuild_seg_grid(room_id: str):
    g = defaultdict(list)
    pl = rooms.get(room_id, {})
    for pid, p in pl.items():
        flat = p.get("snake") or []
        n = len(flat) // 2
        if n < 3:
            continue

        start = max(0, int(IGNORE_OTHER_HEAD_SEGS))
        end = max(start + 1, (n - 1 - int(IGNORE_OTHER_TAIL_SEGS)))
        if end <= start:
            continue

        for i in range(start, end):
            ax = float(flat[2 * i + 0]) + SEGMENT * 0.5
            ay = float(flat[2 * i + 1]) + SEGMENT * 0.5
            bx = float(flat[2 * (i + 1) + 0]) + SEGMENT * 0.5
            by = float(flat[2 * (i + 1) + 1]) + SEGMENT * 0.5

            mnx = min(ax, bx)
            mxx = max(ax, bx)
            mny = min(ay, by)
            mxy = max(ay, by)

            c0x = int(mnx // SEG_GRID_CELL)
            c1x = int(mxx // SEG_GRID_CELL)
            c0y = int(mny // SEG_GRID_CELL)
            c1y = int(mxy // SEG_GRID_CELL)

            for cx in range(c0x, c1x + 1):
                for cy in range(c0y, c1y + 1):
                    g[(cx, cy)].append((pid, i))

    seg_grid[room_id] = g

def head_hits_segments_grid(room_id: str, pid: str, head: dict, r: float) -> bool:
    off = SEGMENT * 0.5
    px = float(head["x"]) + off
    py = float(head["y"]) + off

    cx, cy = seg_cell_of_xy(px, py)
    g = seg_grid.get(room_id) or {}

    rr = float(r)

    for dx in range(-SEG_NEIGHBOR_CELLS, SEG_NEIGHBOR_CELLS + 1):
        for dy in range(-SEG_NEIGHBOR_CELLS, SEG_NEIGHBOR_CELLS + 1):
            for oid, i in g.get((cx + dx, cy + dy), ()):
                if oid == pid:
                    continue
                op = rooms.get(room_id, {}).get(oid)
                if not op:
                    continue
                flat = op.get("snake") or []
                n = len(flat) // 2
                if n < 3:
                    continue

                start = max(0, int(IGNORE_OTHER_HEAD_SEGS))
                end = max(start + 1, (n - 1 - int(IGNORE_OTHER_TAIL_SEGS)))
                denom = max(1, end - start)

                if i < start or i >= end:
                    continue

                ax = float(flat[2 * i + 0]) + off
                ay = float(flat[2 * i + 1]) + off
                bx = float(flat[2 * (i + 1) + 0]) + off
                by = float(flat[2 * (i + 1) + 1]) + off

                prog = (i - start) / denom
                if prog <= 0.60:
                    k_tail = 1.0
                else:
                    t = (prog - 0.60) / 0.40
                    k_tail = 1.0 + (TAIL_RADIUS_SCALE - 1.0) * t

                rr2 = (rr * k_tail) ** 2
                if dist2_point_to_segment(px, py, ax, ay, bx, by) <= rr2:
                    return True
    return False

async def game_loop():
    logging.info("Game loop started")
    next_t = time.perf_counter()
    last_pc = time.perf_counter()

    while True:
        now_pc = time.perf_counter()
        if now_pc < next_t:
            await asyncio.sleep(next_t - now_pc)
            continue
        next_t = now_pc + TICK

        dt = now_pc - last_pc
        last_pc = now_pc
        dt = max(0.010, min(dt, 0.050))
        dt_mul = dt / TICK

        for room_id in list(rooms.keys()):
            players = rooms.get(room_id, {})
            if not players:
                continue

            room_tick[room_id] = (room_tick[room_id] + 1) % 1_000_000

            if food_dirty.get(room_id, False):
                rebuild_food_grid(room_id)
                food_dirty[room_id] = False

            to_kill: list[str] = []
            now = time.time()

            for pid, p in list(players.items()):
                path = p["path"]
                head = p["head"]
                u = p["dir"]
                p["tick_i"] = (p.get("tick_i", 0) + 1) % 10_000

                length = float(p.get("length", 1.0))

                speed = SPEED * dt_mul
                if p.get("boost", False) and length > BOOST_MIN_LEN:
                    speed = SPEED * BOOST_MULT * dt_mul
                else:
                    p["boost"] = False

                nx = head["x"] + u["x"] * speed
                ny = head["y"] + u["y"] * speed

                if nx < 0 or ny < 0 or nx > WORLD_W - SEGMENT or ny > WORLD_H - SEGMENT:
                    to_kill.append(pid)
                    continue

                head["x"], head["y"] = nx, ny

                p["path_ver"] = int(p.get("path_ver", 0)) + 1
                v = int(p["path_ver"])

                added = append_head_point_dense(path, v, nx, ny, PATH_MAX_STEP)
                p["path_len"] = float(p.get("path_len", 0.0)) + float(added)

                cx, cy = cell_of_xy(nx, ny)

                eat_idx: Optional[int] = None
                for idx in iter_neighbor_food_indices(room_id, cx, cy):
                    if idx < 0:
                        continue
                    try:
                        f = foods[room_id][idx]
                    except Exception:
                        continue
                    if can_eat(nx, ny, f, u):
                        eat_idx = idx
                        break

                if eat_idx is not None:
                    f = foods[room_id][eat_idx]
                    p["pending_grow"] = float(p.get("pending_grow", 0.0)) + float(food_growth(f))

                    arr = foods[room_id]
                    last = arr[-1]
                    arr[eat_idx] = last
                    arr.pop()
                    food_dirty[room_id] = True

                    if f.get("kind") == "base":
                        base_food_debt[room_id] += 1
                        ensure_base_food_worker(room_id)

                add_now = min(float(p.get("pending_grow", 0.0)), float(MAX_GROW_PER_TICK))
                if add_now > 0.0:
                    length = float(p.get("length", 1.0)) + add_now
                    p["length"] = float(length)
                    p["pending_grow"] = float(p.get("pending_grow", 0.0)) - add_now

                if float(p["length"]) > float(MAX_LEN):
                    p["length"] = float(MAX_LEN)
                    p["pending_grow"] = 0.0

                # boost drops: keep as 1 segment per drop (game feel), but keep float type consistent
                # --- BOOST COST (smooth) + proportional drop trail ---
                if p.get("boost", False) and float(p["length"]) > BOOST_MIN_LEN:
                    # плавная стоимость буста (учитываем dt_mul, чтобы при лаге не ломало баланс)
                    spend = float(BOOST_COST_PER_TICK) * float(dt_mul)
                    spend = min(spend, float(BOOST_MAX_COST_PER_TICK))

                    if spend > 0.0:
                        # 1) сначала "съедаем" накопленный рост, чтобы буст не обнулял длину мгновенно
                        pg = float(p.get("pending_grow", 0.0))
                        if pg > 0.0:
                            take = min(pg, spend)
                            p["pending_grow"] = pg - take
                            spend -= take

                        # 2) остаток списываем из реальной длины
                        if spend > 0.0:
                            if float(p["length"]) > float(BOOST_MIN_LEN):
                                p["length"] = float(p["length"]) - spend
                            else:
                                p["length"] = float(BOOST_MIN_LEN)

                        # 3) сколько реально потратили в этом тике (всего, включая pending_grow)
                        spent_total = float(BOOST_COST_PER_TICK) * float(dt_mul)
                        spent_total = min(spent_total, float(BOOST_MAX_COST_PER_TICK))

                        p["boost_spent"] = float(p.get("boost_spent", 0.0)) + spent_total

                        # 4) след из еды: 1 drop на каждые 1.0 потраченной "длины"
                        #    так след всегда соответствует расходу
                        while p["boost_spent"] >= 1.0:
                            p["boost_spent"] -= 1.0

                            if count_kind(room_id, "drop") >= DROP_FOOD_CAP:
                                break
                            if len(foods[room_id]) >= TOTAL_FOOD_CAP:
                                break

                            tail = path[-1]
                            tx, ty = float(tail["x"]), float(tail["y"])

                            if len(path) >= 2:
                                prev = path[-2]
                                px, py = float(prev["x"]), float(prev["y"])
                                vx, vy = (tx - px), (ty - py)
                                vl = math.hypot(vx, vy)
                            else:
                                vx, vy, vl = 0.0, 0.0, 0.0

                            if vl < 1e-6:
                                uu = p.get("dir") or {"x": 1.0, "y": 0.0}
                                vx, vy = (-float(uu["x"]), -float(uu["y"]))
                                vl = math.hypot(vx, vy) or 1.0

                            nx2, ny2 = vx / vl, vy / vl
                            lx, ly = -ny2, nx2

                            side_jit = SEGMENT * 0.06
                            j = random.uniform(-side_jit, side_jit)

                            x = tx + lx * j
                            y = ty + ly * j

                            x = max(0.0, min(x, float(WORLD_W - SEGMENT)))
                            y = max(0.0, min(y, float(WORLD_H - SEGMENT)))

                            gx = int(round(x / SEGMENT)) * SEGMENT
                            gy = int(round(y / SEGMENT)) * SEGMENT

                            foods[room_id].append({
                                "x": gx,
                                "y": gy,
                                "color": p["color"],
                                "size": float(BOOST_FOOD_SIZE),
                                "kind": "drop",
                            })
                            food_dirty[room_id] = True

                need_path_len = (float(p["length"]) + 10.0) * SEG_DIST
                trim_path_fast(path, p, need_path_len)

                p["snake"] = build_snake_flat_from_path(path, float(p["length"]))

                if float(p["length"]) < 2.0:
                    to_kill.append(pid)

                p["cell"] = (cx, cy)
                p["seg_cell"] = seg_cell_of_xy(nx + SEGMENT * 0.5, ny + SEGMENT * 0.5)

            rebuild_player_grid(room_id)

            # throttled seg_grid rebuild (still rebuild immediately on deaths below)
            if (room_tick[room_id] % SEG_GRID_EVERY_TICKS) == 0:
                rebuild_seg_grid(room_id)

            for pid, p in list(players.items()):
                if pid in to_kill:
                    continue

                elapsed = now - p.get("spawn_time", 0)
                if elapsed <= SPAWN_PROTECTION:
                    continue

                head = p.get("head")
                if not head:
                    to_kill.append(pid)
                    continue

                if head_hits_segments_grid(room_id, pid, head, HIT_RADIUS):
                    to_kill.append(pid)

            if food_dirty.get(room_id, False):
                rebuild_food_grid(room_id)
                food_dirty[room_id] = False

            killed = set(to_kill)
            if killed:
                for pid in killed:
                    dead_p = players.get(pid)
                    if dead_p:
                        spawn_corpse_food(room_id, dead_p)

                if food_dirty.get(room_id, False):
                    rebuild_food_grid(room_id)
                    food_dirty[room_id] = False

                payload_players_all = {}
                for k, v in players.items():
                    if k in killed:
                        continue
                    payload_players_all[k] = {
                        "snake": v.get("snake", []),
                        "color": v.get("color"),
                        "boost": 1 if v.get("boost") else 0,
                    }

                for pid in killed:
                    dead_p = players.get(pid)
                    dead_head = dead_p.get("head") if dead_p else None

                    if dead_head:
                        last_payload = {
                            "type": "snapshot",
                            "players": payload_players_all,
                            "foods": collect_food_near(room_id, float(dead_head["x"]), float(dead_head["y"])),
                        }
                    else:
                        last_payload = {"type": "snapshot", "players": payload_players_all, "foods": []}

                    ws_dead = connections.get(room_id, {}).pop(pid, None)
                    if ws_dead:
                        t = asyncio.create_task(death_flow(room_id, pid, ws_dead, last_payload))
                        death_tasks.add(t)
                        t.add_done_callback(death_tasks.discard)

                    players.pop(pid, None)

                rebuild_player_grid(room_id)
                rebuild_seg_grid(room_id)

            send_state = (room_tick[room_id] % STATE_SEND_EVERY_TICKS == 0)
            send_foods = (room_tick[room_id] % FOODS_SEND_EVERY == 0)
            send_keyframe = (room_tick[room_id] % KEYFRAME_EVERY_TICKS == 0)

            if not (send_state or send_foods):
                continue

            # per-tick caches (room)
            state_item_cache: Dict[str, dict] = {}
            foods_cache_by_cell: Dict[Tuple[int, int], List[dict]] = {}

            if send_state:
                for pid, p in players.items():
                    if not p.get("head"):
                        continue

                    h = p["head"]
                    u = p["dir"]
                    path = p["path"]

                    tail = []
                    lim = min(PATH_SEND_LAST_N, len(path))
                    for i in range(lim):
                        node = path[i]
                        tail.append([int(node.get("v", 0)), float(node["x"]), float(node["y"])])

                    lf = float(p.get("length", 1.0))

                    item = {
                        "h": [float(h["x"]), float(h["y"])],
                        "u": [float(u["x"]), float(u["y"])],
                        "lf": lf,
                        "l": int(round(lf)),
                        "b": 1 if p.get("boost") else 0,
                        "pv": int(p.get("path_ver", 0)),
                        "pt": tail,
                        "c": p.get("color"),
                    }

                    if send_keyframe:
                        item["kf"] = 1
                        if lf <= float(MAX_KEYFRAME_LEN):
                            item["body"] = p.get("snake", [])

                    state_item_cache[pid] = item

            conns = connections.get(room_id, {})
            for viewer_pid in list(conns.keys()):
                pp = players.get(viewer_pid)
                if not pp or not pp.get("head"):
                    continue

                payload = {"type": "state"}

                if send_state:
                    vcx, vcy = pp["cell"]
                    near = collect_players_near(room_id, vcx, vcy)

                    pl_out = {}
                    for pid in near:
                        it = state_item_cache.get(pid)
                        if it is not None:
                            pl_out[pid] = it
                    payload["players"] = pl_out

                if send_foods:
                    hx = float(pp["head"]["x"])
                    hy = float(pp["head"]["y"])
                    fc = cell_of_xy(hx, hy)
                    cached = foods_cache_by_cell.get(fc)
                    if cached is None:
                        cached = collect_food_near(room_id, hx, hy)
                        foods_cache_by_cell[fc] = cached
                    payload["foods"] = cached

                await enqueue_send(room_id, viewer_pid, payload)

@app.on_event("startup")
async def startup():
    asyncio.create_task(game_loop())
