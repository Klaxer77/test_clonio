# =========================
# main.py (FULL) — COLLISIONS “ВПРИТЫК” + DEATH SNAPSHOT (чтобы видно было corpse-еду)
#
# Что сделано:
# 1) Коллизия: точка головы vs сегменты пути другого игрока (point->segment),
#    чтобы смерть была максимально “по касанию”, без ранних срабатываний.
# 2) HIT_RADIUS уменьшен до более “впритык”.
# 3) IGNORE_OTHER_HEAD_LEN включён, чтобы не ловить странности около головы соперника.
# 4) ВАЖНО ДЛЯ ВИЗУАЛА: перед смертью умершему отправляется последний snapshot мира
#    (где уже заспавнилась corpse-еда), потом короткая пауза, потом {"type":"death"} и close().
# =========================

from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse
import asyncio, random, time, logging, math
from collections import deque

logging.basicConfig(level=logging.INFO)
app = FastAPI()

WORLD_W = 10000
WORLD_H = 10000
SEGMENT = 30
TICK = 0.025

FOOD_COUNT = 4000
FOOD_RESPAWN = 70
GROW_AMOUNT = 1

SPEED = 8
SPAWN_PROTECTION = 0

# буст
BOOST_MULT = 1.8
BOOST_MIN_LEN = 6
BOOST_DROP_EVERY_TICKS = 2
BOOST_FOOD_SIZE = 1.2

# дистанция между сегментами (для отрисовки)
SEG_DIST = SEGMENT * 0.85

# лимиты еды
DROP_FOOD_CAP = 500
TOTAL_FOOD_CAP = FOOD_COUNT + DROP_FOOD_CAP

# рост от drop-еды
DROP_GROW = 1

# как быстро длина прибавляется (сегментов за тик)
MAX_GROW_PER_TICK = 1

# денсификация пути (как часто добавляем узлы пути)
PATH_MAX_STEP = SEG_DIST * 0.75

# еда от мёртвой змеи
CORPSE_FOOD_SIZE = 1.25
CORPSE_GROW_MULT = 2
CORPSE_STEP = 2
CORPSE_JITTER = SEGMENT * 0.18

# коллизия “голова в тело”
# было 1.6 — слишком “далеко”. Здесь ближе к касанию.
HIT_RADIUS = SEGMENT * 1.10
# игнорируем кусок около головы чужой змеи (чтобы не ловить странности в упор)
IGNORE_OTHER_HEAD_LEN = SEG_DIST * 1.5

# смерть: чтобы клиент увидел corpse-еду перед закрытием
DEATH_SNAPSHOT_DELAY = 0.20   # пауза после отправки last_payload
DEATH_AFTER_DELAY = 0.10      # пауза после {"type":"death"} перед close()

rooms: dict[str, dict[str, dict]] = {}
connections: dict[str, dict[str, WebSocket]] = {}
foods: dict[str, list[dict]] = {}  # room_id -> list[food]


def collide_aabb(a, b, delta=SEGMENT * 0.9) -> bool:
    return abs(a["x"] - b["x"]) < delta and abs(a["y"] - b["y"]) < delta


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


async def respawn_base_food(room_id: str):
    await asyncio.sleep(FOOD_RESPAWN)
    if room_id not in foods:
        return
    if count_kind(room_id, "base") >= FOOD_COUNT:
        return
    if len(foods[room_id]) >= TOTAL_FOOD_CAP:
        return
    foods[room_id].append(random_food(1.0, "base"))


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
        try:
            size = float(food.get("size", CORPSE_FOOD_SIZE))
        except Exception:
            size = CORPSE_FOOD_SIZE
        size = max(0.5, min(size, 6.0))
        return max(1, int(round(GROW_AMOUNT * size * CORPSE_GROW_MULT)))

    try:
        size = float(food.get("size", 1.0))
    except Exception:
        size = 1.0
    size = max(0.25, min(size, 5.0))
    return max(1, int(round(GROW_AMOUNT * size)))


# ---------------------------
# Геометрия
# ---------------------------

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


def head_hits_other_path(head: dict, other_path: deque, r: float, ignore_head_len: float) -> bool:
    """
    Точка головы vs отрезки пути другого игрока.
    Это максимально близко к “касанию”, без ранних срабатываний от отрезка движения.
    """
    if not other_path or len(other_path) < 3:
        return False

    off = SEGMENT * 0.5
    px, py = float(head["x"]) + off, float(head["y"]) + off
    rr2 = float(r) * float(r)

    acc = 0.0
    for i in range(len(other_path) - 1):
        a = other_path[i]
        b = other_path[i + 1]

        ax, ay = float(a["x"]) + off, float(a["y"]) + off
        bx, by = float(b["x"]) + off, float(b["y"]) + off

        seg_len = math.hypot(bx - ax, by - ay)
        if seg_len < 1e-6:
            continue

        if acc < ignore_head_len:
            acc += seg_len
            continue

        if dist2_point_to_segment(px, py, ax, ay, bx, by) <= rr2:
            return True

        acc += seg_len

    return False


# ---------------------------
# Тело по пути головы
# ---------------------------

def _append_path_node(path: deque, x: float, y: float):
    if not path:
        path.appendleft({"x": x, "y": y, "ds": 0.0})
        return

    hx = path[0]["x"]
    hy = path[0]["y"]
    ds = math.hypot(x - hx, y - hy)
    if ds < 1e-6:
        return
    path.appendleft({"x": x, "y": y, "ds": ds})


def append_head_point_dense(path: deque, x: float, y: float, max_step: float = PATH_MAX_STEP):
    if not path:
        path.appendleft({"x": x, "y": y, "ds": 0.0})
        return

    hx = path[0]["x"]
    hy = path[0]["y"]
    dx = x - hx
    dy = y - hy
    d = math.hypot(dx, dy)
    if d < 1e-6:
        return

    if d <= max_step:
        _append_path_node(path, x, y)
        return

    steps = max(2, int(math.ceil(d / max_step)))
    for k in range(1, steps + 1):
        t = k / steps
        _append_path_node(path, hx + dx * t, hy + dy * t)


def path_total_len(path: deque) -> float:
    total = 0.0
    for i in range(1, len(path)):
        total += float(path[i]["ds"])
    return total


def trim_path(path: deque, need_len: float):
    while len(path) > 2:
        total = path_total_len(path)
        if total <= need_len:
            break
        path.pop()


def sample_point(path: deque, dist_from_head: float) -> dict:
    if not path:
        return {"x": 0.0, "y": 0.0}

    if dist_from_head <= 0:
        return {"x": path[0]["x"], "y": path[0]["y"]}

    acc = 0.0
    for i in range(len(path) - 1):
        a = path[i]
        b = path[i + 1]
        seg_len = float(b["ds"])
        if seg_len <= 1e-6:
            continue

        if acc + seg_len >= dist_from_head:
            t = (dist_from_head - acc) / seg_len
            x = a["x"] + (b["x"] - a["x"]) * t
            y = a["y"] + (b["y"] - a["y"]) * t
            return {"x": x, "y": y}

        acc += seg_len

    last = path[-1]
    return {"x": last["x"], "y": last["y"]}


def build_snake_from_path(path: deque, length_segments: int) -> list[dict]:
    snake = []
    n = max(1, int(length_segments))
    for i in range(n):
        p = sample_point(path, i * SEG_DIST)
        snake.append({"x": p["x"], "y": p["y"]})
    return snake


def spawn_corpse_food(room_id: str, p: dict):
    if room_id not in foods:
        return
    body = p.get("snake") or []
    if len(body) < 2:
        return

    free = max(0, TOTAL_FOOD_CAP - len(foods[room_id]))
    if free <= 0:
        return

    points = body[::max(1, int(CORPSE_STEP))]
    if len(points) > free:
        step2 = int(math.ceil(len(points) / free))
        points = points[::max(1, step2)]

    color = p.get("color")
    for seg in points:
        if len(foods[room_id]) >= TOTAL_FOOD_CAP:
            break

        jx = random.uniform(-CORPSE_JITTER, CORPSE_JITTER)
        jy = random.uniform(-CORPSE_JITTER, CORPSE_JITTER)

        x = int((float(seg["x"]) + jx) // SEGMENT) * SEGMENT
        y = int((float(seg["y"]) + jy) // SEGMENT) * SEGMENT

        x = max(0, min(x, WORLD_W - SEGMENT))
        y = max(0, min(y, WORLD_H - SEGMENT))

        foods[room_id].append({
            "x": x,
            "y": y,
            "color": color,
            "size": float(CORPSE_FOOD_SIZE),
            "kind": "corpse",
        })


@app.get("/")
async def index():
    with open("index.html", encoding="utf-8") as f:
        return HTMLResponse(f.read())


@app.websocket("/ws/{room_id}/{player_id}")
async def ws_handler(ws: WebSocket, room_id: str, player_id: str):
    await ws.accept()
    logging.info(f"[{player_id}] Connected to room {room_id}")

    if room_id not in rooms:
        rooms[room_id] = {}
        connections[room_id] = {}
        foods[room_id] = [random_food(1.0, "base") for _ in range(FOOD_COUNT)]

    x = random.randint(8, (WORLD_W // SEGMENT) - 8) * SEGMENT
    y = random.randint(8, (WORLD_H // SEGMENT) - 8) * SEGMENT

    path = deque()
    path.appendleft({"x": float(x), "y": float(y), "ds": 0.0})

    for i in range(1, 14):
        px = float(x - i * (SEG_DIST * 0.9))
        py = float(y)
        prev = path[-1]
        ds = math.hypot(px - prev["x"], py - prev["y"])
        path.append({"x": px, "y": py, "ds": ds})

    rooms[room_id][player_id] = {
        "dir": {"x": 1.0, "y": 0.0},
        "color": f"hsl({random.randint(0,360)},80%,50%)",
        "spawn_time": time.time(),
        "boost": False,
        "tick_i": 0,

        "path": path,
        "head": {"x": float(x), "y": float(y)},
        "length": 10,
        "pending_grow": 0,
        "snake": [],
    }
    connections[room_id][player_id] = ws

    try:
        while True:
            data = await ws.receive_json()
            p = rooms[room_id].get(player_id)
            if not p:
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
    except Exception as e:
        logging.info(f"[{player_id}] Error: {e}")
        rooms[room_id].pop(player_id, None)
        connections[room_id].pop(player_id, None)


async def game_loop():
    logging.info("Game loop started")
    while True:
        await asyncio.sleep(TICK)

        for room_id in list(rooms.keys()):
            players = rooms.get(room_id, {})
            if not players:
                continue

            to_kill: list[str] = []
            now = time.time()

            # 1) движение + еда + рост/буст + сборка snake
            for pid, p in list(players.items()):
                path = p["path"]
                head = p["head"]
                u = p["dir"]
                p["tick_i"] = (p.get("tick_i", 0) + 1) % 10_000

                speed = SPEED
                if p.get("boost", False) and p["length"] > BOOST_MIN_LEN:
                    speed = SPEED * BOOST_MULT
                else:
                    p["boost"] = False

                nx = head["x"] + u["x"] * speed
                ny = head["y"] + u["y"] * speed

                if nx < 0 or ny < 0 or nx > WORLD_W - SEGMENT or ny > WORLD_H - SEGMENT:
                    logging.info(f"OUT_OF_BOUNDS: {pid}")
                    to_kill.append(pid)
                    continue

                head["x"], head["y"] = nx, ny
                append_head_point_dense(path, nx, ny, PATH_MAX_STEP)

                # --- ЕДА ---
                for food in list(foods[room_id]):
                    if collide_aabb({"x": nx, "y": ny}, food):
                        p["pending_grow"] += int(food_growth(food))
                        foods[room_id].remove(food)
                        if food.get("kind") == "base":
                            asyncio.create_task(respawn_base_food(room_id))
                        break

                # --- РОСТ ---
                add_now = min(int(p["pending_grow"]), MAX_GROW_PER_TICK)
                if add_now > 0:
                    p["length"] += add_now
                    p["pending_grow"] -= add_now

                # --- БУСТ ---
                if p.get("boost", False) and p["length"] > BOOST_MIN_LEN:
                    if p["tick_i"] % BOOST_DROP_EVERY_TICKS == 0:
                        if p["pending_grow"] > 0:
                            p["pending_grow"] = max(0, int(p["pending_grow"]) - 1)
                        else:
                            if p["length"] > BOOST_MIN_LEN:
                                tail_pos = sample_point(path, (p["length"] - 1) * SEG_DIST)
                                p["length"] -= 1

                                if count_kind(room_id, "drop") < DROP_FOOD_CAP and len(foods[room_id]) < TOTAL_FOOD_CAP:
                                    foods[room_id].append({
                                        "x": int(tail_pos["x"] // SEGMENT) * SEGMENT,
                                        "y": int(tail_pos["y"] // SEGMENT) * SEGMENT,
                                        "color": p["color"],
                                        "size": float(BOOST_FOOD_SIZE),
                                        "kind": "drop",
                                    })

                need_path_len = (p["length"] + 10) * SEG_DIST
                trim_path(path, need_path_len)
                p["snake"] = build_snake_from_path(path, p["length"])

                if p["length"] < 2:
                    to_kill.append(pid)

            # 2) коллизии: точка головы vs чужой path
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

                for oid, op in list(players.items()):
                    if pid == oid:
                        continue

                    other_path = op.get("path")
                    if not other_path or len(other_path) < 3:
                        continue

                    if head_hits_other_path(head, other_path, HIT_RADIUS, IGNORE_OTHER_HEAD_LEN):
                        logging.info(f"COLLISION: {pid} -> {oid}")
                        to_kill.append(pid)
                        break

            # 3) убитые: corpse-еда + last snapshot (с едой) умершему + death + close + удалить
            for pid in set(to_kill):
                dead_p = players.get(pid)
                if dead_p:
                    spawn_corpse_food(room_id, dead_p)

                # last payload после спавна еды, но до удаления игрока
                payload_players = {
                    k: {
                        "snake": v["snake"],
                        "color": v["color"],
                        "boost": bool(v.get("boost", False)),
                    }
                    for k, v in players.items()
                    if k != pid  # умершего можно убрать из кадра
                }
                last_payload = {"players": payload_players, "foods": foods[room_id]}

                ws_dead = connections.get(room_id, {}).get(pid)
                if ws_dead:
                    try:
                        await ws_dead.send_json(last_payload)
                        await asyncio.sleep(DEATH_SNAPSHOT_DELAY)
                        await ws_dead.send_json({"type": "death"})
                        await asyncio.sleep(DEATH_AFTER_DELAY)
                        await ws_dead.close()
                    except Exception:
                        pass

                connections.get(room_id, {}).pop(pid, None)
                players.pop(pid, None)

            # 4) рассылка всем живым
            payload_players = {
                pid: {
                    "snake": p["snake"],
                    "color": p["color"],
                    "boost": bool(p.get("boost", False)),
                }
                for pid, p in players.items()
            }
            payload = {"players": payload_players, "foods": foods[room_id]}

            for sock in list(connections.get(room_id, {}).values()):
                try:
                    await sock.send_json(payload)
                except Exception:
                    pass


@app.on_event("startup")
async def startup():
    asyncio.create_task(game_loop())
