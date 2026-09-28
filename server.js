/**
 * TIDEWALK - server (authoritative for dice, turns, moves, rooms, coins, cooldowns)
 *
 * RULES (N = 4 or 5 players, each with 4 tokens)
 *  - Ring track has L = 13*N squares. Seat s starts on square 13*s.
 *  - Token progress p: -1 = in the yard; 0..L-2 = on the ring (square (13*s+p) % L);
 *    L-1..L+3 = 5-square home path; L+4 = FIN (finished). A token needs an exact roll to reach FIN.
 *  - A 6 is needed to leave the yard (token goes to p=0).
 *  - Safe squares: each seat's start square (idx%13==0) and idx%13==8. Tokens there cannot be captured.
 *  - Landing on a non-safe ring square captures every opponent token on it (they go back to the yard).
 *  - Extra turn after: rolling a 6, capturing, or reaching FIN. Three 6s in a row forfeit the turn.
 *  - One legal move is applied automatically; several legal moves -> the player chooses a token.
 *  - A seat finishes when all 4 tokens are at FIN. Finish order gives places. When N-1 seats have
 *    finished, the remaining seat is last and the game ends.
 *  - Turn timer 25s: on timeout the server plays the best move for that player.
 *  - Disconnect: 60s grace to reconnect (turns are auto-played meanwhile). After that, or if a
 *    player leaves mid-game, the seat is "abandoned": the server auto-plays it. The entry fee is
 *    NOT refunded after the game starts. A returning (timed-out) player can retake their seat.
 *
 * COINS: integers only. Entry fee deducted from everyone at START. Winner gets 2x entry, last gets 0,
 * the middle places split the rest equally; any indivisible remainder is kept by the game and shown.
 * Every change is a ledger transaction.
 */
const express = require('express'), http = require('http'), fs = require('fs'), path = require('path'), crypto = require('crypto');
const { Server } = require('socket.io');
const app = express();
app.use(express.static(path.join(__dirname, 'public')));
const server = http.createServer(app);
const io = new Server(server);

const START_COINS = 2500, CLAIM_COINS = 100, CLAIM_MS = 5 * 60 * 1000;
const ENTRIES = [120, 300, 500, 1000, 2000], SEG = 13, TURN_MS = 25000, GRACE_MS = 60000, AVATARS = 7;
const DB_FILE = process.env.DB_FILE || path.join(__dirname, 'data.json');

// ---------- storage (JSON file; swap for PostgreSQL/Supabase for permanent storage) ----------
let db = { players: {}, ledger: [] };
try { db = JSON.parse(fs.readFileSync(DB_FILE, 'utf8')); } catch {}
let dirty = false;
const save = () => { dirty = true; };
setInterval(() => { if (dirty) { dirty = false; fs.writeFile(DB_FILE, JSON.stringify(db), () => {}); } }, 2000);
const id = (n = 8) => crypto.randomBytes(n).toString('hex');
const bySecret = new Map(Object.values(db.players).map(p => [p.secret, p]));

class U extends Error {}                       // user-facing error
const fail = m => { throw new U(m); };

// ---------- coin ledger: the ONLY place balances change ----------
// types: PLAYER_ENTRY, GAME_PRIZE, FREE_CLAIM, REFUND, ADMIN_ADJUSTMENT
function tx(p, type, amount, gameId) {
  if (!Number.isSafeInteger(amount)) throw new Error('Non-integer amount');
  const before = p.coins;
  if (before + amount < 0) fail('Not enough coins.');
  p.coins = before + amount;
  db.ledger.push({ id: id(6), playerId: p.id, amount, type, gameId: gameId || null, ts: Date.now(), before, after: p.coins });
  save();
}
function payoutPlan(n, E) {
  if (![4, 5].includes(n) || !Number.isSafeInteger(E) || E <= 0) fail('Invalid room setup.');
  const pool = n * E, win = 2 * E, mid = n - 2, rest = pool - win;
  if (rest < 0) fail('Payout error: the prize pool cannot cover the winner prize.');
  const each = Math.floor(rest / mid), remainder = rest - each * mid;
  const prizes = [win, ...Array(mid).fill(each), 0];
  if (prizes.reduce((a, b) => a + b, 0) + remainder !== pool) fail('Payout error: the pool does not balance.');
  return { pool, prizes, remainder };
}

// ---------- state ----------
const rooms = new Map(), socketsByPid = new Map();
const meOf = p => ({ id: p.id, name: p.name, avatar: p.avatar, coins: p.coins, claimIn: Math.max(0, (p.lastClaim || 0) + CLAIM_MS - Date.now()) });
const pushMe = p => { const s = socketsByPid.get(p.id); if (s) s.emit('me', meOf(p)); };
const activeRoom = p => { const r = p.roomCode && rooms.get(p.roomCode); return r && (r.status === 'WAITING' || r.status === 'PLAYING') ? r : null; };
const newCode = () => { for (;;) { const c = String(crypto.randomInt(100000, 1000000)); if (!rooms.has(c)) return c; } };
const nm = (r, s) => db.players[r.seats[s].pid].name;
const ord = n => ['', '1st', '2nd', '3rd', '4th', '5th'][n];

function pub(r) {
  let plan = null, planError = null;
  try { plan = payoutPlan(r.max, r.entry); } catch (e) { planError = e.message; }
  const g = r.g;
  return {
    code: r.code, hostId: r.hostId, max: r.max, entry: r.entry, status: r.status, gameId: r.gameId, created: r.created,
    plan, planError, remainder: r.remainder || 0,
    seats: r.seats.map((s, i) => { const p = db.players[s.pid]; return { seat: i, pid: s.pid, name: p.name, avatar: p.avatar, coins: p.coins, connected: s.connected, abandoned: !!s.abandoned }; }),
    g: g && { tokens: g.tokens, turn: g.turn, phase: g.phase, dice: g.dice, legal: g.legal, finished: g.finished, lastRoll: g.lastRoll, log: g.log, left: Math.max(0, g.deadline - Date.now()), results: g.results }
  };
}
const bcast = r => io.to(r.code).emit('room', pub(r));

function seatPlayer(r, p) {
  r.seats.push({ pid: p.id, connected: true });
  p.roomCode = r.code;
  const s = socketsByPid.get(p.id); if (s) s.join(r.code);
  bcast(r);
}
function leave(r, p) {
  const i = r.seats.findIndex(s => s.pid === p.id), sock = socketsByPid.get(p.id);
  if (sock) { sock.leave(r.code); sock.emit('room', null); }
  if (r.status === 'WAITING' && i >= 0) {
    r.seats.splice(i, 1);                      // entry is only charged at START, so nothing to refund here
    if (!r.seats.length) { r.status = 'CANCELLED'; r.closeAt = Date.now() + 60000; }
    else if (r.hostId === p.id) r.hostId = r.seats[0].pid;
  } else if (r.status === 'PLAYING' && i >= 0) {
    r.seats[i].abandoned = true; r.seats[i].left = true;
    r.g.log = `${p.name} left. The table plays for them.`;
    if (r.g.turn === i) r.g.deadline = Math.min(r.g.deadline, Date.now() + 900);
  }
  p.roomCode = null;
  bcast(r);
}

// ---------- game logic ----------
function initGame(r) {
  r.g = { tokens: r.seats.map(() => [-1, -1, -1, -1]), turn: crypto.randomInt(r.max), phase: 'roll', dice: null, legal: [], sixes: 0,
    finished: [], lastRoll: null, log: '', deadline: Date.now() + TURN_MS, results: null };
  r.g.log = `${nm(r, r.g.turn)} goes first.`;
}
function legalMoves(r, seat, d) {
  const L = SEG * r.max, FIN = L + 4, out = [];
  r.g.tokens[seat].forEach((p, t) => {
    if (p === FIN) return;
    if (p === -1 ? d === 6 : p + d <= FIN) out.push(t);
  });
  return out;
}
function nextTurn(r, same) {
  const g = r.g;
  g.legal = []; g.phase = 'roll';
  if (!same) {
    g.sixes = 0;
    do { g.turn = (g.turn + 1) % r.max; } while (g.finished.includes(g.turn));
  }
  g.deadline = Date.now() + (r.seats[g.turn].abandoned ? 900 : TURN_MS);
}
function doRoll(r) {
  const g = r.g, d = crypto.randomInt(1, 7), name = nm(r, g.turn);
  g.dice = d; g.lastRoll = { seat: g.turn, d, n: (g.lastRoll ? g.lastRoll.n : 0) + 1 };
  g.sixes = d === 6 ? g.sixes + 1 : 0;
  if (g.sixes >= 3) { g.log = `${name} rolled a third 6 and loses the turn.`; return nextTurn(r, false); }
  const legal = legalMoves(r, g.turn, d);
  if (!legal.length) { g.log = `${name} rolled ${d}. No move available.`; return nextTurn(r, false); }
  g.legal = legal;
  if (legal.length === 1) return doMove(r, legal[0]);
  g.phase = 'move'; g.deadline = Date.now() + (r.seats[g.turn].abandoned ? 900 : TURN_MS);
  g.log = `${name} rolled ${d}. Choose a token.`;
}
function doMove(r, t) {
  const g = r.g, n = r.max, L = SEG * n, FIN = L + 4, seat = g.turn, d = g.dice, tk = g.tokens[seat], name = nm(r, seat);
  const to = tk[t] === -1 ? 0 : tk[t] + d; tk[t] = to;
  let cap = 0;
  if (to <= L - 2) {
    const idx = (SEG * seat + to) % L;
    if (idx % SEG !== 0 && idx % SEG !== 8)
      g.tokens.forEach((o, s) => { if (s !== seat) o.forEach((q, k) => { if (q >= 0 && q <= L - 2 && (SEG * s + q) % L === idx) { o[k] = -1; cap++; } }); });
  }
  g.log = cap ? `${name} rolled ${d} and sent ${cap} token${cap > 1 ? 's' : ''} back to the yard!` : `${name} rolled ${d}.`;
  if (tk.every(q => q === FIN)) {
    g.finished.push(seat); g.log = `${name} is home in ${ord(g.finished.length)} place!`;
    if (g.finished.length === n - 1) {
      g.finished.push([...Array(n).keys()].find(s => !g.finished.includes(s)));
      return endGame(r);
    }
    return nextTurn(r, false);
  }
  nextTurn(r, d === 6 || cap > 0 || to === FIN);
}
function endGame(r) {
  const g = r.g, plan = payoutPlan(r.max, r.entry);
  g.results = g.finished.map((seat, i) => ({ seat, pos: i + 1, name: nm(r, seat), prize: plan.prizes[i], net: plan.prizes[i] - r.entry }));
  g.results.forEach(x => { const p = db.players[r.seats[x.seat].pid]; if (x.prize > 0) tx(p, 'GAME_PRIZE', x.prize, r.gameId); pushMe(p); });
  r.remainder = plan.remainder; r.status = 'FINISHED'; r.closeAt = Date.now() + 10 * 60000; g.phase = 'done'; g.legal = [];
  g.log = 'Game finished.';
}
function auto(r) {
  const g = r.g;
  if (g.phase === 'roll') return doRoll(r);
  if (g.phase !== 'move') return;
  const best = g.legal.reduce((a, t) => (g.tokens[g.turn][t] > g.tokens[g.turn][a] ? t : a), g.legal[0]);
  doMove(r, best);
}

setInterval(() => {
  const now = Date.now();
  for (const r of [...rooms.values()]) {
    if (r.status === 'WAITING') {
      r.seats.filter(s => !s.connected && now - s.dcAt > 20000).forEach(s => leave(r, db.players[s.pid]));
    } else if (r.status === 'PLAYING') {
      let ch = false;
      r.seats.forEach((s, i) => {
        if (!s.connected && !s.abandoned && now - s.dcAt > GRACE_MS) {
          s.abandoned = true; r.g.log = `${nm(r, i)} timed out. The table plays for them.`; ch = true;
          if (r.g.turn === i) r.g.deadline = Math.min(r.g.deadline, now + 900);
        }
      });
      if (now >= r.g.deadline) { auto(r); ch = true; }
      if (ch) bcast(r);
    }
    if ((r.status === 'FINISHED' || r.status === 'CANCELLED') && now > r.closeAt) {
      r.seats.forEach(s => { const p = db.players[s.pid]; if (p && p.roomCode === r.code) p.roomCode = null; });
      rooms.delete(r.code);
    }
  }
}, 500);

// ---------- sockets ----------
io.on('connection', socket => {
  const on = (ev, fn) => socket.on(ev, (d, cb) => {
    try { const r = fn(d || {}) || {}; if (typeof cb === 'function') cb({ ok: true, ...r }); }
    catch (e) { if (!(e instanceof U)) console.error(e); if (typeof cb === 'function') cb({ error: e instanceof U ? e.message : 'Something went wrong.' }); }
  });
  const P = () => db.players[socket.data.pid] || fail('Not signed in.');
  const inGame = () => {
    const p = P(), r = activeRoom(p);
    if (!r || r.status !== 'PLAYING') fail('No game in progress.');
    return { p, r, i: r.seats.findIndex(s => s.pid === p.id) };
  };

  on('hello', d => {
    let p = d.secret && bySecret.get(String(d.secret));
    if (!p) {
      const name = String(d.name || '').trim().slice(0, 14);
      if (!name) fail('Enter a name to start.');
      p = { id: id(4), secret: id(16), name, avatar: crypto.randomInt(AVATARS), coins: 0, lastClaim: 0, roomCode: null };
      db.players[p.id] = p; bySecret.set(p.secret, p);
      tx(p, 'ADMIN_ADJUSTMENT', START_COINS, null);            // starting balance
    }
    socket.data.pid = p.id; socketsByPid.set(p.id, socket);
    const r = p.roomCode && rooms.get(p.roomCode);
    const seat = r && r.seats.find(s => s.pid === p.id);
    if (seat && (r.status === 'WAITING' || r.status === 'PLAYING')) {   // reconnect: same identity, same seat
      seat.connected = true; seat.abandoned = false; socket.join(r.code); bcast(r);
    }
    return { secret: p.secret, me: meOf(p), room: r && seat ? pub(r) : null };
  });

  on('claim', () => {
    const p = P();
    if (p.lastClaim + CLAIM_MS - Date.now() > 0) fail('Free coins are not ready yet.');
    p.lastClaim = Date.now();                                     // server clock only
    tx(p, 'FREE_CLAIM', CLAIM_COINS, null);
    pushMe(p);
  });

  on('createRoom', d => {
    const p = P(); if (activeRoom(p)) fail('You are already in a game.');
    const max = +d.max, entry = +d.entry;
    if (![4, 5].includes(max) || !ENTRIES.includes(entry)) fail('Invalid room setup.');
    if (p.coins < entry) fail('Not enough coins.');
    const r = { code: newCode(), hostId: p.id, max, entry, status: 'WAITING', created: Date.now(), gameId: null, seats: [], g: null };
    rooms.set(r.code, r); seatPlayer(r, p);
  });

  on('joinRoom', d => {
    const p = P(), r = rooms.get(String(d.code || '').trim());
    if (!r || r.status === 'CANCELLED') fail('Room not found.');
    if (r.seats.some(s => s.pid === p.id)) return;
    if (activeRoom(p)) fail('You are already in a game.');
    if (r.status !== 'WAITING') fail('Game already started.');
    if (r.seats.length >= r.max) fail('Room is full.');
    if (p.coins < r.entry) fail(`You need ${r.entry - p.coins} more coins.`);
    seatPlayer(r, p);
  });

  on('leaveRoom', () => { const p = P(), r = p.roomCode && rooms.get(p.roomCode); if (r) leave(r, p); else { p.roomCode = null; socket.emit('room', null); } });

  on('start', () => {
    const p = P(), r = activeRoom(p);
    if (!r || r.status !== 'WAITING') fail('No room to start.');
    if (r.hostId !== p.id) fail('Only the host can start the game.');
    if (r.seats.length !== r.max) fail(`Waiting for ${r.max - r.seats.length} more player(s).`);
    if (r.seats.some(s => !s.connected)) fail('A player is disconnected.');
    payoutPlan(r.max, r.entry);                                   // throws a readable error if the payout is invalid
    const ps = r.seats.map(s => db.players[s.pid]), poor = ps.find(q => q.coins < r.entry);
    if (poor) fail(`${poor.name} does not have enough coins.`);
    r.status = 'STARTING'; r.gameId = id(6);
    ps.forEach(q => tx(q, 'PLAYER_ENTRY', -r.entry, r.gameId));
    initGame(r); r.status = 'PLAYING';
    ps.forEach(pushMe); bcast(r);
  });

  on('roll', () => {
    const { r, i } = inGame();
    if (r.g.turn !== i) fail('It is not your turn.');
    if (r.g.phase !== 'roll') fail('Choose a token to move.');
    doRoll(r); bcast(r);
  });

  on('move', d => {
    const { r, i } = inGame(), t = +d.token;
    if (r.g.turn !== i) fail('It is not your turn.');
    if (r.g.phase !== 'move') fail('Roll the die first.');
    if (!r.g.legal.includes(t)) fail('That token cannot move.');
    doMove(r, t); bcast(r);
  });

  socket.on('disconnect', () => {
    const pid = socket.data.pid; if (!pid) return;
    if (socketsByPid.get(pid) === socket) socketsByPid.delete(pid);
    const p = db.players[pid], r = p.roomCode && rooms.get(p.roomCode), s = r && r.seats.find(x => x.pid === pid);
    if (s) { s.connected = false; s.dcAt = Date.now(); bcast(r); }
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log('Tidewalk running on port ' + PORT));
