// Push-optimal Sokoban solver for make.fun sokoban-solver-01.
// Levels are rooms off a one-square hallway; a box pushed through a door
// never returns, so each room is solved on its own and the optima add up.
// Inside a room, breadth-first search over pushes only: a state is the
// boxes plus the player's reachable region (its lowest square). Dead
// squares and frozen 2x2 blocks are pruned. The search is bounded by
// work, never by the clock, so two runs write the same bytes.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const INPUT = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const MAX_STATES = 250_000;
type Dir = [number, number, string, string];
const DIRS: Dir[] = [[0, -1, 'u', 'U'], [0, 1, 'd', 'D'], [-1, 0, 'l', 'L'], [1, 0, 'r', 'R']];
interface Level { w: number; h: number; wall: Uint8Array; goals: number[]; boxes: number[]; player: number; }

function parseLevel(text: string): Level {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals: number[] = [];
  const boxes: number[] = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x];
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
  }
  boxes.sort((a, b) => a - b);
  goals.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player };
}

function liveSquares(level: Level): Uint8Array {
  const { w, wall, goals } = level;
  const live = new Uint8Array(wall.length);
  const queue = [...goals];
  for (const g of goals) live[g] = 1;
  for (let qi = 0; qi < queue.length; qi++) {
    const x = queue[qi];
    for (const [dx, dy] of DIRS) {
      const d = dy * w + dx;
      const y = x - d;
      if (y >= 0 && y < wall.length && !wall[y] && !wall[y - d] && !live[y]) {
        live[y] = 1;
        queue.push(y);
      }
    }
  }
  return live;
}

function reach(level: Level, occupied: Uint8Array, from: number, seen: Int32Array, stamp: number, stack: Int32Array): number {
  const { w, wall } = level;
  let low = from;
  let n = 0;
  stack[n++] = from;
  seen[from] = stamp;
  while (n > 0) {
    const p = stack[--n];
    if (p < low) low = p;
    for (const [dx, dy] of DIRS) {
      const q = p + dy * w + dx;
      if (!wall[q] && !occupied[q] && seen[q] !== stamp) {
        seen[q] = stamp;
        stack[n++] = q;
      }
    }
  }
  return low;
}

function frozenBlock(level: Level, occupied: Uint8Array, goal: Uint8Array, t: number): boolean {
  const { w, wall } = level;
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const b = a + 1, c = a + w, d = c + 1;
    if (!((wall[a] || occupied[a]) && (wall[b] || occupied[b]) && (wall[c] || occupied[c]) && (wall[d] || occupied[d]))) continue;
    if ((occupied[a] && !goal[a]) || (occupied[b] && !goal[b]) || (occupied[c] && !goal[c]) || (occupied[d] && !goal[d])) return true;
  }
  return false;
}

function walkTo(level: Level, occupied: Uint8Array, from: number, to: number): string {
  if (from === to) return '';
  const { w, wall } = level;
  const prev = new Int32Array(wall.length).fill(-1);
  const how = new Array<string>(wall.length);
  const queue = [from];
  prev[from] = from;
  for (let qi = 0; qi < queue.length; qi++) {
    const p = queue[qi];
    if (p === to) break;
    for (const [dx, dy, letter] of DIRS) {
      const q = p + dy * w + dx;
      if (wall[q] || occupied[q] || prev[q] !== -1) continue;
      prev[q] = p;
      how[q] = letter;
      queue.push(q);
    }
  }
  if (prev[to] === -1) throw new Error('walkTo: push square out of reach');
  let s = '';
  for (let p = to; p !== from; p = prev[p]) s = how[p] + s;
  return s;
}

function endOf(w: number, from: number, moves: string): number {
  let p = from;
  for (const ch of moves.toLowerCase()) p += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
  return p;
}

function solvePushOptimal(level: Level, maxStates: number): { pushes: number; moves: string } | null {
  const { w, wall, goals } = level;
  const size = wall.length;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const live = liveSquares(level);
  if (level.boxes.some((b) => !live[b])) return null;
  const solved = (boxes: number[]): boolean => boxes.every((b) => goal[b]);
  if (solved(level.boxes)) return { pushes: 0, moves: '' };
  const pack = (boxes: number[]): number => {
    let k = 0;
    for (const b of boxes) k = k * size + b;
    return k;
  };
  const unpack = (packed: number, n: number): number[] => {
    const boxes = new Array<number>(n);
    let k = packed;
    for (let i = n - 1; i >= 0; i--) { boxes[i] = k % size; k = Math.floor(k / size); }
    return boxes;
  };
  const keyOf = (boxes: number[], low: number): number => {
    let k = low;
    for (const b of boxes) k = k * size + b;
    return k;
  };
  const occupied = new Uint8Array(size);
  const seen = new Int32Array(size);
  const mark = new Int32Array(size);
  const stack = new Int32Array(size);
  let stamp = 0, markStamp = 0;
  const packedBoxes: number[] = [pack(level.boxes)];
  const statePlayer: number[] = [level.player];
  const parent: number[] = [-1];
  const moveFrom: number[] = [-1];
  const moveTo: number[] = [-1];
  const visited = new Map<number, number>();
  for (const b of level.boxes) occupied[b] = 1;
  const startLow = reach(level, occupied, level.player, seen, ++stamp, stack);
  for (const b of level.boxes) occupied[b] = 0;
  visited.set(keyOf(level.boxes, startLow), 0);
  let found = -1;
  for (let head = 0; found < 0 && head < packedBoxes.length; head++) {
    const boxes = unpack(packedBoxes[head], level.boxes.length);
    for (const b of boxes) occupied[b] = 1;
    const regionStamp = ++stamp;
    reach(level, occupied, statePlayer[head], seen, regionStamp, stack);
    for (let bi = 0; bi < boxes.length && found < 0; bi++) {
      const b = boxes[bi];
      for (const [dx, dy] of DIRS) {
        const d = dy * w + dx;
        const t = b + d;
        const from = b - d;
        if (seen[from] !== regionStamp || wall[t] || occupied[t] || !live[t]) continue;
        occupied[b] = 0;
        occupied[t] = 1;
        const frozen = frozenBlock(level, occupied, goal, t);
        let key = -1, nextPacked = 0;
        if (!frozen) {
          const next = boxes.slice();
          next[bi] = t;
          next.sort((a, bb) => a - bb);
          nextPacked = pack(next);
          key = keyOf(next, reach(level, occupied, b, mark, ++markStamp, stack));
        }
        occupied[t] = 0;
        occupied[b] = 1;
        if (frozen || visited.has(key)) continue;
        if (packedBoxes.length >= maxStates) {
          for (const x of boxes) occupied[x] = 0;
          return null;
        }
        visited.set(key, packedBoxes.length);
        packedBoxes.push(nextPacked);
        statePlayer.push(b);
        parent.push(head);
        moveFrom.push(b);
        moveTo.push(t);
        if (solved(unpack(nextPacked, level.boxes.length))) { found = packedBoxes.length - 1; break; }
      }
    }
    for (const x of boxes) occupied[x] = 0;
  }
  if (found < 0) return null;
  const path: number[] = [];
  for (let s = found; s > 0; s = parent[s]) path.push(s);
  path.reverse();
  let moves = '';
  let player = level.player;
  let boxes = level.boxes.slice();
  for (const s of path) {
    const from = moveFrom[s], to = moveTo[s], d = to - from;
    const dir = DIRS.find(([dx, dy]) => dy * w + dx === d) ?? DIRS[0];
    for (const b of boxes) occupied[b] = 1;
    moves += walkTo(level, occupied, player, from - d);
    for (const b of boxes) occupied[b] = 0;
    moves += dir[3];
    player = from;
    boxes = unpack(packedBoxes[s], level.boxes.length);
  }
  return { pushes: path.length, moves };
}

interface Room { boxes: number[]; goals: number[]; done: boolean; }

function roomsOf(level: Level): Room[] | null {
  const { w, wall, goals, boxes, player } = level;
  const live = liveSquares(level);
  const row = Math.floor(player / w);
  const cut = new Uint8Array(wall.length);
  for (let i = row * w; i < (row + 1) * w; i++) if (!wall[i] && !live[i]) cut[i] = 1;
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(wall.length).fill(-1);
  const rooms: Room[] = [];
  for (let s = 0; s < wall.length; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const squares = [s];
    part[s] = rooms.length;
    for (let i = 0; i < squares.length; i++) {
      for (const [dx, dy] of DIRS) {
        const q = squares[i] + dy * w + dx;
        if (!wall[q] && !cut[q] && part[q] < 0) { part[q] = rooms.length; squares.push(q); }
      }
    }
    rooms.push({ boxes: [], goals: [], done: false });
  }
  for (const b of boxes) {
    if (part[b] < 0) return null;
    rooms[part[b]].boxes.push(b);
  }
  for (const g of goals) {
    if (part[g] < 0) return null;
    rooms[part[g]].goals.push(g);
  }
  if (rooms.some((r) => r.boxes.length !== r.goals.length)) return null;
  return rooms.filter((r) => r.boxes.length > 0);
}

function solveByRooms(level: Level): string | null {
  const rooms = roomsOf(level);
  if (rooms === null) {
    const whole = solvePushOptimal(level, MAX_STATES);
    return whole === null ? null : whole.moves;
  }
  let player = level.player;
  let moves = '';
  for (const room of rooms) {
    const wall = level.wall.slice();
    for (const other of rooms) {
      if (other === room) continue;
      for (const b of other.done ? other.goals : other.boxes) wall[b] = 1;
    }
    const sub: Level = { w: level.w, h: level.h, wall, goals: room.goals.slice().sort((a, b) => a - b), boxes: room.boxes.slice().sort((a, b) => a - b), player };
    const solved = solvePushOptimal(sub, MAX_STATES);
    if (solved === null) return null;
    moves += solved.moves;
    player = endOf(level.w, player, solved.moves);
    room.done = true;
  }
  return moves;
}

function solve(text: string): string {
  const moves = solveByRooms(parseLevel(text));
  return moves ?? '';
}

for (const id of readdirSync(INPUT).sort()) {
  const moves = solve(readFileSync(join(INPUT, id, 'level.txt'), 'utf8'));
  mkdirSync(join(OUTPUT, id), { recursive: true });
  writeFileSync(join(OUTPUT, id, 'solution.txt'), `${moves}\n`);
}
