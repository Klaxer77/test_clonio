from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse
import asyncio, random, time, logging, math
from collections import deque, defaultdict
from typing import Dict, Tuple, Set, Optional, List, Deque

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

# boost
BOOST_MULT = 1.8
BOOST_MIN_LEN = 6
BOOST_DROP_EVERY_TICKS = 2
BOOST_FOOD_SIZE = 1.2

SEG_DIST = SEGMENT * 0.85

DROP_FOOD_CAP = 500
TOTAL_FOOD_CAP = FOOD_COUNT + DROP_FOOD_CAP

DROP_GROW = 1
MAX_GROW_PER_TICK = 1

PATH_MAX_STEP = SEG_DIST * 1.4

# corpse food
CORPSE_FOOD_SIZE = 1.7
CORPSE_GROW_MULT = 4.0
CORPSE_STEP = 3
CORPSE_JITTER = SEGMENT * 0.14
CORPSE_MAX_PER_DEATH = 130

# ---------- HIT / COLLISION ----------
# Было SEGMENT*1.10, это реально жирно и даёт "умер далеко"
HIT_RADIUS = SEGMENT * 0.95 * 1.35

# игнор головы соперника: в сегментах, когда считаем по snake
IGNORE_OTHER_HEAD_SEGS = 1

# игнор хвоста соперника: чтобы хвост не был "липким"
IGNORE_OTHER_TAIL_SEGS = 0

# ближе к хвосту уменьшаем радиус
TAIL_RADIUS_SCALE = 1.25

# EAT
EAT_RADIUS = SEGMENT * 0.75
EAT_RADIUS2 = EAT_RADIUS * EAT_RADIUS

DEATH_SNAPSHOT_DELAY = 0.20
DEATH_AFTER_DELAY = 0.10

# ---- OPT ----
GRID_CELL = int(SEGMENT * 10)        # 300px
PLAYER_NEIGHBOR_CELLS = 2            # 5x5 вокруг
SEND_TIMEOUT_SEC = 0.03              # таймаут на send_json

MAX_LEN = 450
FOODS_SEND_EVERY = 4
PLAYERS_SEND_EVERY = 1

FOOD_VIEW_CELLS = 8

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


def cell_of_xy(x: float, y: float) -> Tuple[int, int]:
    return int(x // GRID_CELL), int(y // GRID_CELL)


def random_food(size: float = 1.0, kind: str = "base"):
    return {
        "x": random.randint(0, WORLD_W // SEGMENT - 1) * SEGMENT,
        "y": random.randint(0, WORLD_H // SEGMENT - 1) * SEGMENT,
        "color": f"hsl({random.randint(0,360)},80%,60%)",
        "size": float(size),
        "kind": kind,  # "base" | "drop" | "corpse"
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

        # сколько базовой надо добить до нормы
        base_now = count_kind(room_id, "base")
        need = max(0, FOOD_COUNT - base_now)
        if need <= 0:
            base_food_debt[room_id] = 0
            return

        # сколько реально можем добавить сейчас
        can_add = min(
            base_food_debt[room_id],
            need,
            max(1, FOOD_COUNT // 25),  # пачка (например 20 при FOOD_COUNT=500)
        )

        # если упёрлись в общий лимит — просто ждём
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


def food_growth(food: dict) -> int:
    kind = food.get("kind", "base")

    if kind == "drop":
        return DROP_GROW

    if kind == "corpse":
        # фиксированный большой прирост, не зависит от size
        return max(1, int(round(GROW_AMOUNT * CORPSE_GROW_MULT)))

    try:
        size = float(food.get("size", 1.0))
    except Exception:
        size = 1.0
    size = max(0.25, min(size, 5.0))
    return max(1, int(round(GROW_AMOUNT * size)))



def can_eat(head_x: float, head_y: float, food: dict) -> bool:
    hx = float(head_x) + SEGMENT * 0.5
    hy = float(head_y) + SEGMENT * 0.5
    fx = float(food["x"]) + SEGMENT * 0.5
    fy = float(food["y"]) + SEGMENT * 0.5
    dx = hx - fx
    dy = hy - fy
    return (dx * dx + dy * dy) <= EAT_RADIUS2


def snake_build_every(length: int) -> int:
    return 1


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


def head_hits_other_snake(
    head: dict,
    other_snake: List[dict],
    r: float,
    ignore_head_segments: int,
    ignore_tail_segments: int,
) -> bool:
    if not other_snake or len(other_snake) < 3:
        return False

    off = SEGMENT * 0.5
    px, py = float(head["x"]) + off, float(head["y"]) + off

    n = len(other_snake)
    start = max(0, int(ignore_head_segments))
    end = max(start + 1, (n - 1 - int(ignore_tail_segments)))

    denom = max(1, end - start)

    for i in range(start, end):
        a = other_snake[i]
        b = other_snake[i + 1]

        ax, ay = float(a["x"]) + off, float(a["y"]) + off
        bx, by = float(b["x"]) + off, float(b["y"]) + off

        prog = (i - start) / denom  # 0 у "ближе к голове", 1 у "ближе к хвосту"

        # после 60% длины начинаем плавно усиливать радиус к хвосту
        if prog <= 0.60:
            k_tail = 1.0
        else:
            t = (prog - 0.60) / 0.40  # 0..1
            k_tail = 1.0 + (TAIL_RADIUS_SCALE - 1.0) * t


        rr2 = (float(r) * k_tail) ** 2
        if dist2_point_to_segment(px, py, ax, ay, bx, by) <= rr2:
            return True

    return False


def _append_path_node(path: Deque[dict], x: float, y: float) -> float:
    if not path:
        path.appendleft({"x": x, "y": y, "ds": 0.0})
        return 0.0

    hx = path[0]["x"]
    hy = path[0]["y"]
    ds = math.hypot(x - hx, y - hy)
    if ds < 1e-6:
        return 0.0

    path.appendleft({"x": x, "y": y, "ds": ds})
    return ds


def append_head_point_dense(path: Deque[dict], x: float, y: float, max_step: float = PATH_MAX_STEP) -> float:
    if not path:
        path.appendleft({"x": x, "y": y, "ds": 0.0})
        return 0.0

    hx = path[0]["x"]
    hy = path[0]["y"]
    dx = x - hx
    dy = y - hy
    d = math.hypot(dx, dy)
    if d < 1e-6:
        return 0.0

    if d <= max_step:
        return _append_path_node(path, x, y)

    added = 0.0
    steps = max(2, int(math.ceil(d / max_step)))
    for k in range(1, steps + 1):
        t = k / steps
        added += _append_path_node(path, hx + dx * t, hy + dy * t)
    return added


def trim_path_fast(path: Deque[dict], p: dict, need_len: float):
    while len(path) > 2 and float(p.get("path_len", 0.0)) > need_len:
        last = path.pop()
        p["path_len"] = float(p.get("path_len", 0.0)) - float(last.get("ds", 0.0))
        if p["path_len"] < 0:
            p["path_len"] = 0.0


def build_snake_from_path_fast(path: Deque[dict], length_segments: int) -> list:
    n = max(1, int(length_segments))
    if not path:
        return [{"x": 0.0, "y": 0.0}]

    out: List[dict] = []
    want = 0.0

    a = path[0]
    ax, ay = float(a["x"]), float(a["y"])
    out.append({"x": ax, "y": ay})
    if n == 1:
        return out

    acc = 0.0
    for i in range(len(path) - 1):
        b = path[i + 1]
        bx, by = float(b["x"]), float(b["y"])
        seg_len = float(b.get("ds", 0.0))
        if seg_len <= 1e-6:
            ax, ay = bx, by
            continue

        while len(out) < n and (acc + seg_len) >= (want + SEG_DIST):
            want += SEG_DIST
            t = (want - acc) / seg_len
            x = ax + (bx - ax) * t
            y = ay + (by - ay) * t
            out.append({"x": x, "y": y})

        acc += seg_len
        ax, ay = bx, by
        if len(out) >= n:
            break

    last = path[-1]
    lx, ly = float(last["x"]), float(last["y"])
    while len(out) < n:
        out.append({"x": lx, "y": ly})

    return out


def spawn_corpse_food(room_id: str, p: dict):
    if room_id not in foods:
        return
    body = p.get("snake") or []
    if len(body) < 2:
        return

    arr = foods[room_id]
    free = max(0, TOTAL_FOOD_CAP - len(arr))
    if free <= 0:
        return

    players_cnt = len(rooms.get(room_id, {}))
    adapt = max(70, int(CORPSE_MAX_PER_DEATH * (1.0 if players_cnt <= 6 else 0.7)))
    spawn_cap = min(int(adapt), int(free))
    if spawn_cap <= 0:
        return

    step = max(1, int(CORPSE_STEP))
    points = body[::step]
    if len(points) > spawn_cap:
        stride = max(1, int(math.floor(len(points) / spawn_cap)))
        points = points[::stride]
        if len(points) > spawn_cap:
            points = points[:spawn_cap]

    color = p.get("color")

    for seg in points:
        if len(arr) >= TOTAL_FOOD_CAP:
            break

        jx = random.uniform(-CORPSE_JITTER, CORPSE_JITTER)
        jy = random.uniform(-CORPSE_JITTER, CORPSE_JITTER)

        x = int((float(seg["x"]) + jx) // SEGMENT) * SEGMENT
        y = int((float(seg["y"]) + jy) // SEGMENT) * SEGMENT

        x = max(0, min(x, WORLD_W - SEGMENT))
        y = max(0, min(y, WORLD_H - SEGMENT))

        arr.append({
            "x": x,
            "y": y,
            "color": color,
            "size": float(CORPSE_FOOD_SIZE),
            "kind": "corpse",
        })

    food_dirty[room_id] = True


@app.get("/")
async def index():
    with open("index.html", encoding="utf-8") as f:
        return HTMLResponse(f.read())


async def safe_send(sock: WebSocket, payload: dict):
    try:
        await asyncio.wait_for(sock.send_json(payload), timeout=SEND_TIMEOUT_SEC)
    except Exception:
        pass


async def death_flow(ws: WebSocket, last_payload: dict):
    try:
        await safe_send(ws, last_payload)
        await asyncio.sleep(DEATH_SNAPSHOT_DELAY)
        await safe_send(ws, {"type": "death"})
        await asyncio.sleep(DEATH_AFTER_DELAY)
        await ws.close()
    except Exception:
        pass


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
    path.appendleft({"x": float(x), "y": float(y), "ds": 0.0})

    init_path_len = 0.0
    for i in range(1, 14):
        px = float(x - i * (SEG_DIST * 0.9))
        py = float(y)
        prev = path[-1]
        ds = math.hypot(px - prev["x"], py - prev["y"])
        path.append({"x": px, "y": py, "ds": ds})
        init_path_len += ds

    rooms[room_id][player_id] = {
        "dir": {"x": 1.0, "y": 0.0},
        "color": f"hsl({random.randint(0,360)},80%,50%)",
        "spawn_time": time.time(),
        "boost": False,
        "tick_i": 0,

        "path": path,
        "path_len": init_path_len,
        "head": {"x": float(x), "y": float(y)},
        "length": 10,
        "pending_grow": 0,
        "snake": [],

        "cell": cell_of_xy(x, y),
    }
    connections[room_id][player_id] = ws
    rebuild_player_grid(room_id)

    try:
        while True:
            data = await ws.receive_json()
            p = rooms[room_id].get(player_id)
            if not p:
                continue

            if data.get("type") == "ping":
                await safe_send(ws, {"type": "pong", "t": data.get("t", 0)})
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
        rooms[room_id].pop(player_id, None)
        connections[room_id].pop(player_id, None)
        rebuild_player_grid(room_id)
    except Exception as e:
        logging.info(f"[{player_id}] Error: {e}")
        rooms[room_id].pop(player_id, None)
        connections[room_id].pop(player_id, None)
        rebuild_player_grid(room_id)


def iter_neighbor_players(room_id: str, cx: int, cy: int):
    g = player_grid.get(room_id) or {}
    for dx in range(-PLAYER_NEIGHBOR_CELLS, PLAYER_NEIGHBOR_CELLS + 1):
        for dy in range(-PLAYER_NEIGHBOR_CELLS, PLAYER_NEIGHBOR_CELLS + 1):
            for pid in g.get((cx + dx, cy + dy), ()):
                yield pid


def iter_neighbor_food_indices(room_id: str, cx: int, cy: int):
    g = food_grid.get(room_id) or {}
    for dx in range(-1, 2):
        for dy in range(-1, 2):
            for idx in g.get((cx + dx, cy + dy), ()):
                yield idx


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

            # 1) movement + eat + grow/boost + snake build
            for pid, p in list(players.items()):
                path = p["path"]
                head = p["head"]
                u = p["dir"]
                p["tick_i"] = (p.get("tick_i", 0) + 1) % 10_000

                speed = SPEED * dt_mul
                if p.get("boost", False) and p["length"] > BOOST_MIN_LEN:
                    speed = SPEED * BOOST_MULT * dt_mul
                else:
                    p["boost"] = False

                nx = head["x"] + u["x"] * speed
                ny = head["y"] + u["y"] * speed

                if nx < 0 or ny < 0 or nx > WORLD_W - SEGMENT or ny > WORLD_H - SEGMENT:
                    to_kill.append(pid)
                    continue

                head["x"], head["y"] = nx, ny

                added = append_head_point_dense(path, nx, ny, PATH_MAX_STEP)
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
                    if can_eat(nx, ny, f):
                        eat_idx = idx
                        break

                if eat_idx is not None:
                    f = foods[room_id][eat_idx]
                    p["pending_grow"] += int(food_growth(f))

                    arr = foods[room_id]
                    last = arr[-1]
                    arr[eat_idx] = last
                    arr.pop()
                    food_dirty[room_id] = True

                    if f.get("kind") == "base":
                        base_food_debt[room_id] += 1
                        ensure_base_food_worker(room_id)

                add_now = min(int(p["pending_grow"]), MAX_GROW_PER_TICK)
                if add_now > 0:
                    p["length"] += add_now
                    p["pending_grow"] -= add_now

                if p["length"] > MAX_LEN:
                    p["length"] = MAX_LEN
                    p["pending_grow"] = 0

                if p.get("boost", False) and p["length"] > BOOST_MIN_LEN:
                    if p["tick_i"] % BOOST_DROP_EVERY_TICKS == 0:
                        if p["pending_grow"] > 0:
                            p["pending_grow"] = max(0, int(p["pending_grow"]) - 1)
                        else:
                            if p["length"] > BOOST_MIN_LEN:
                                tail = path[-1]
                                p["length"] -= 1

                                if count_kind(room_id, "drop") < DROP_FOOD_CAP and len(foods[room_id]) < TOTAL_FOOD_CAP:
                                    foods[room_id].append({
                                        "x": int(float(tail["x"]) // SEGMENT) * SEGMENT,
                                        "y": int(float(tail["y"]) // SEGMENT) * SEGMENT,
                                        "color": p["color"],
                                        "size": float(BOOST_FOOD_SIZE),
                                        "kind": "drop",
                                    })
                                    food_dirty[room_id] = True

                need_path_len = (p["length"] + 10) * SEG_DIST
                trim_path_fast(path, p, need_path_len)

                p["snake"] = build_snake_from_path_fast(path, p["length"])

                if p["length"] < 2:
                    to_kill.append(pid)

                p["cell"] = (cx, cy)

            rebuild_player_grid(room_id)

            # 2) collisions (по SNAKE, а не по path)
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

                cx, cy = p.get("cell", cell_of_xy(head["x"], head["y"]))

                for oid in iter_neighbor_players(room_id, cx, cy):
                    if oid == pid:
                        continue
                    op = players.get(oid)
                    if not op:
                        continue

                    other_snake = op.get("snake") or []
                    if len(other_snake) < 3:
                        continue

                    if head_hits_other_snake(
                        head=head,
                        other_snake=other_snake,
                        r=HIT_RADIUS,
                        ignore_head_segments=IGNORE_OTHER_HEAD_SEGS,
                        ignore_tail_segments=IGNORE_OTHER_TAIL_SEGS,
                    ):
                        to_kill.append(pid)
                        break

            if food_dirty.get(room_id, False):
                rebuild_food_grid(room_id)
                food_dirty[room_id] = False

            # 3) kills (НЕ БЛОЧИМ game_loop)
            killed = set(to_kill)
            if killed:
                for pid in killed:
                    dead_p = players.get(pid)
                    if dead_p:
                        spawn_corpse_food(room_id, dead_p)

                if food_dirty.get(room_id, False):
                    rebuild_food_grid(room_id)
                    food_dirty[room_id] = False

                payload_players_all = {
                    k: {"snake": v["snake"], "color": v["color"], "boost": bool(v.get("boost", False))}
                    for k, v in players.items()
                    if k not in killed
                }

                for pid in killed:
                    dead_p = players.get(pid)
                    dead_head = dead_p.get("head") if dead_p else None

                    if dead_head:
                        last_payload = {
                            "players": payload_players_all,
                            "foods": collect_food_near(room_id, float(dead_head["x"]), float(dead_head["y"])),
                        }
                    else:
                        last_payload = {"players": payload_players_all, "foods": []}

                    ws_dead = connections.get(room_id, {}).pop(pid, None)
                    if ws_dead:
                        t = asyncio.create_task(death_flow(ws_dead, last_payload))
                        death_tasks.add(t)
                        t.add_done_callback(death_tasks.discard)

                    players.pop(pid, None)

                rebuild_player_grid(room_id)

            # 4) broadcast
            send_foods = (room_tick[room_id] % FOODS_SEND_EVERY == 0)
            send_players = (room_tick[room_id] % PLAYERS_SEND_EVERY == 0)

            payload_players = None
            if send_players:
                payload_players = {
                    pid: {"snake": p["snake"], "color": p["color"], "boost": bool(p.get("boost", False))}
                    for pid, p in players.items()
                }

            tasks = []
            conns = connections.get(room_id, {})
            for pid, sock in list(conns.items()):
                payload = {}

                if send_players:
                    payload["players"] = payload_players

                if send_foods:
                    pp = players.get(pid)
                    if pp and pp.get("head"):
                        hx = float(pp["head"]["x"])
                        hy = float(pp["head"]["y"])
                        payload["foods"] = collect_food_near(room_id, hx, hy)
                    else:
                        payload["foods"] = []

                if payload:
                    tasks.append(safe_send(sock, payload))

            if tasks:
                await asyncio.gather(*tasks, return_exceptions=True)


@app.on_event("startup")
async def startup():
    asyncio.create_task(game_loop())
