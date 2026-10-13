(() => {
  'use strict';

  // ---------- Einstellungen ----------
  const TILE = 32, W = 48, H = 36;
  const DAY_LEN = 100;       // Sekunden pro Tag
  const WIN_DAY = 6;         // Tag 6 erreicht = 5 Tage überlebt
  const ZOOM = 1.5;
  const FIRE_MAX = 120;      // maximale Brenndauer in Sekunden
  const PLAYER_R = 9;
  const RECIPES = {
    axe:  { wood: 4,  stone: 2 },
    fire: { wood: 5,  stone: 2 },
    hut:  { wood: 12, stone: 6 },
  };

  // ---------- Hilfsfunktionen ----------
  const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
  const smooth = (a, b, x) => { const t = clamp((x - a) / (b - a), 0, 1); return t * t * (3 - 2 * t); };
  const hash = (x, y) => {
    let h = (x * 374761393 + y * 668265263) | 0;
    h = (h ^ (h >>> 13)) * 1274126177 | 0;
    return ((h ^ (h >>> 16)) >>> 0) / 4294967296;
  };
  function mulberry32(a) {
    return () => {
      a |= 0; a = a + 0x6D2B79F5 | 0;
      let t = Math.imul(a ^ a >>> 15, 1 | a);
      t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
      return ((t ^ t >>> 14) >>> 0) / 4294967296;
    };
  }
  function makeNoise(rand, size) {
    const g = [];
    for (let i = 0; i < (size + 1) * (size + 1); i++) g.push(rand());
    return (x, y) => {
      const fx = x * size, fy = y * size;
      const x0 = Math.floor(fx), y0 = Math.floor(fy);
      const sx = fx - x0, sy = fy - y0;
      const s = t => t * t * (3 - 2 * t);
      const a = g[y0 * (size + 1) + x0], b = g[y0 * (size + 1) + x0 + 1];
      const c = g[(y0 + 1) * (size + 1) + x0], d = g[(y0 + 1) * (size + 1) + x0 + 1];
      const tx = s(sx), ty = s(sy);
      return (a + (b - a) * tx) * (1 - ty) + (c + (d - c) * tx) * ty;
    };
  }

  // ---------- DOM ----------
  const $ = id => document.getElementById(id);
  const canvas = $('game');
  const ctx = canvas.getContext('2d');
  const dark = document.createElement('canvas');
  const dctx = dark.getContext('2d');
  const ui = {
    health: $('bar-health'), hunger: $('bar-hunger'),
    day: $('day'), phase: $('phase'),
    wood: $('inv-wood'), stone: $('inv-stone'), berries: $('inv-berries'), axe: $('inv-axe'),
    status: $('status'), toast: $('toast'),
    overlay: $('overlay'), title: $('ov-title'), text: $('ov-text'), help: $('ov-help'), start: $('ov-start'),
  };
  const craftButtons = document.querySelectorAll('.craft-btn');
  craftButtons.forEach(b => { b.dataset.label = b.querySelector('small').textContent; });

  let dpr = 1, viewW = 0, viewH = 0;
  function resize() {
    dpr = window.devicePixelRatio || 1;
    canvas.width = Math.floor(innerWidth * dpr);
    canvas.height = Math.floor(innerHeight * dpr);
    dark.width = canvas.width;
    dark.height = canvas.height;
    viewW = innerWidth / ZOOM;
    viewH = innerHeight / ZOOM;
  }
  window.addEventListener('resize', resize);
  resize();

  // ---------- Spielzustand ----------
  let state = 'menu';       // menu | play | over | win
  let world, shallow, objects, fires, hut, player;
  let inv, hunger, health, day, dayTime, hasAxe, cooldown, darkness, warm, target, warnedNight;
  let camX = 0, camY = 0, time = 0, toastTimer = 0;
  const keys = {};

  const maxHp = type => (type === 'bush' ? 1 : 4);

  function newGame() {
    const rand = mulberry32(Math.floor(Math.random() * 1e9));
    const noise = makeNoise(rand, 6);

    world = [];
    for (let y = 0; y < H; y++) {
      const row = [];
      for (let x = 0; x < W; x++) {
        const dx = (x - W / 2) / (W / 2), dy = (y - H / 2) / (H / 2);
        const v = 1 - Math.hypot(dx, dy) + (noise(x / W, y / H) - 0.5) * 0.55;
        row.push(v < 0.12 ? 0 : v < 0.22 ? 1 : 2);
      }
      world.push(row);
    }

    const at = (x, y) => (x < 0 || y < 0 || x >= W || y >= H) ? 0 : world[y][x];
    shallow = world.map((row, y) => row.map((t, x) =>
      t === 0 && (at(x + 1, y) || at(x - 1, y) || at(x, y + 1) || at(x, y - 1)) ? 1 : 0));

    const cx = W * TILE / 2, cy = H * TILE / 2;
    objects = [];
    for (let y = 1; y < H - 1; y++) {
      for (let x = 1; x < W - 1; x++) {
        if (world[y][x] !== 2) continue;
        let nearWater = false;
        for (let oy = -1; oy <= 1; oy++) for (let ox = -1; ox <= 1; ox++) if (at(x + ox, y + oy) === 0) nearWater = true;
        if (nearWater) continue;
        const px = x * TILE + TILE / 2 + (rand() - 0.5) * 10;
        const py = y * TILE + TILE / 2 + (rand() - 0.5) * 10;
        if (Math.hypot(px - cx, py - cy) < TILE * 3) continue;
        const r = rand();
        const type = r < 0.08 ? 'tree' : r < 0.11 ? 'rock' : r < 0.14 ? 'bush' : null;
        if (type) objects.push({ type, x: px, y: py, hp: maxHp(type), state: 'full', timer: 0, shake: 0 });
      }
    }

    fires = [];
    hut = null;
    player = { x: cx, y: cy, face: 1, moving: false };
    inv = { wood: 0, stone: 0, berries: 0 };
    hunger = 100; health = 100;
    day = 1; dayTime = 0; hasAxe = false; cooldown = 0;
    darkness = 0; warm = false; target = null; warnedNight = false;
    camX = player.x - viewW / 2;
    camY = player.y - viewH / 2;
  }

  // ---------- Kollision ----------
  function solidAt(px, py) {
    const tx = Math.floor(px / TILE), ty = Math.floor(py / TILE);
    if (tx < 0 || ty < 0 || tx >= W || ty >= H) return true;
    return world[ty][tx] === 0;
  }
  function collides(x, y) {
    const r = PLAYER_R;
    if (solidAt(x - r, y - r) || solidAt(x + r, y - r) || solidAt(x - r, y + r) || solidAt(x + r, y + r)) return true;
    for (const o of objects) {
      if (o.state !== 'full' || o.type === 'bush') continue;
      if (Math.hypot(o.x - x, o.y - y) < 13 + r * 0.6) return true;
    }
    return false;
  }

  // ---------- Aktionen ----------
  function toast(msg) {
    ui.toast.textContent = msg;
    ui.toast.classList.add('show');
    toastTimer = 2.2;
  }

  function findTarget() {
    let best = null, bd = 46;
    for (const o of objects) {
      if (o.state !== 'full') continue;
      const d = Math.hypot(o.x - player.x, o.y - player.y);
      if (d < bd) { bd = d; best = { kind: 'obj', obj: o, x: o.x, y: o.y - (o.type === 'tree' ? 22 : 8) }; }
    }
    for (const f of fires) {
      const d = Math.hypot(f.x - player.x, f.y - player.y);
      if (d < bd) { bd = d; best = { kind: 'fire', fire: f, x: f.x, y: f.y - 28 }; }
    }
    return best;
  }

  function act() {
    if (state !== 'play' || cooldown > 0 || !target) return;
    cooldown = 0.3;
    if (target.kind === 'fire') {
      if (inv.wood < 1) { toast('Du brauchst Holz fürs Feuer'); return; }
      inv.wood--;
      target.fire.fuel = Math.min(FIRE_MAX, target.fire.fuel + 30);
      toast('Holz nachgelegt');
      return;
    }
    const o = target.obj;
    o.hp -= (o.type !== 'bush' && hasAxe) ? 2 : 1;
    o.shake = 0.25;
    if (o.hp > 0) return;
    o.state = 'empty';
    if (o.type === 'tree') { const n = hasAxe ? 3 : 2; inv.wood += n; o.timer = 120; toast(`+${n} Holz`); }
    if (o.type === 'rock') { const n = hasAxe ? 2 : 1; inv.stone += n; o.timer = 180; toast(`+${n} Stein`); }
    if (o.type === 'bush') { inv.berries += 2; o.timer = 60; toast('+2 Beeren'); }
  }

  const canAfford = r => inv.wood >= r.wood && inv.stone >= r.stone;

  function craft(id) {
    if (state !== 'play') return;
    if (id === 'axe' && hasAxe) { toast('Du hast schon eine Axt'); return; }
    if (id === 'hut' && hut) { toast('Du hast schon eine Hütte'); return; }
    const r = RECIPES[id];
    if (!canAfford(r)) { toast('Dir fehlen Materialien'); return; }
    inv.wood -= r.wood; inv.stone -= r.stone;
    if (id === 'axe') { hasAxe = true; toast('Axt hergestellt: du sammelst schneller'); }
    if (id === 'fire') { fires.push({ x: player.x, y: player.y + 8, fuel: 80 }); toast('Lagerfeuer angezündet'); }
    if (id === 'hut') { hut = { x: player.x, y: player.y + 6 }; toast('Hütte gebaut: hier bist du nachts sicher'); }
  }

  function eat() {
    if (state !== 'play') return;
    if (inv.berries < 1) { toast('Du hast keine Beeren'); return; }
    if (hunger > 95) { toast('Du bist satt'); return; }
    inv.berries--;
    hunger = Math.min(100, hunger + 25);
  }

  // ---------- Spielablauf ----------
  function startGame() {
    newGame();
    state = 'play';
    ui.overlay.classList.add('hidden');
  }

  function end(kind) {
    state = kind;
    if (kind === 'win') {
      ui.title.textContent = 'Geschafft!';
      ui.text.textContent = `Du hast ${WIN_DAY - 1} Tage auf der Insel überlebt.`;
    } else {
      ui.title.textContent = 'Du hast es nicht geschafft';
      ui.text.textContent = `Du hast ${day - 1} von ${WIN_DAY - 1} Tagen überstanden. Bleib nachts bei einem Feuer oder deiner Hütte und vergiss das Essen nicht.`;
    }
    ui.help.classList.add('hidden');
    ui.start.textContent = 'Nochmal spielen';
    ui.overlay.classList.remove('hidden');
  }

  function update(dt) {
    time += dt;
    if (toastTimer > 0) { toastTimer -= dt; if (toastTimer <= 0) ui.toast.classList.remove('show'); }
    if (state !== 'play') return;

    cooldown = Math.max(0, cooldown - dt);

    // Bewegung
    let dx = 0, dy = 0;
    if (keys['a'] || keys['arrowleft']) dx -= 1;
    if (keys['d'] || keys['arrowright']) dx += 1;
    if (keys['w'] || keys['arrowup']) dy -= 1;
    if (keys['s'] || keys['arrowdown']) dy += 1;
    player.moving = !!(dx || dy);
    if (player.moving) {
      const l = Math.hypot(dx, dy);
      dx /= l; dy /= l;
      const sp = 110;
      if (!collides(player.x + dx * sp * dt, player.y)) player.x += dx * sp * dt;
      if (!collides(player.x, player.y + dy * sp * dt)) player.y += dy * sp * dt;
      if (dx) player.face = dx > 0 ? 1 : -1;
    }

    // Tageszeit
    dayTime += dt;
    if (dayTime >= DAY_LEN) {
      dayTime -= DAY_LEN;
      day++;
      warnedNight = false;
      if (day >= WIN_DAY) { end('win'); return; }
      toast(`Tag ${day} beginnt`);
    }
    const t = dayTime / DAY_LEN;
    darkness = smooth(0.55, 0.68, t) - smooth(0.88, 1.0, t);
    if (t > 0.5 && !warnedNight) { warnedNight = true; toast('Die Nacht naht. Zünde ein Lagerfeuer an (2)'); }

    // Objekte und Feuer
    for (const o of objects) {
      if (o.shake > 0) o.shake = Math.max(0, o.shake - dt);
      if (o.state === 'empty') { o.timer -= dt; if (o.timer <= 0) { o.state = 'full'; o.hp = maxHp(o.type); } }
    }
    for (const f of fires) f.fuel = Math.max(0, f.fuel - dt);

    // Wärme
    warm = fires.some(f => f.fuel > 0 && Math.hypot(f.x - player.x, f.y - player.y) < 120) ||
           (hut && Math.hypot(hut.x - player.x, hut.y - player.y) < 100);

    // Interaktion
    target = findTarget();
    if (keys['e'] || keys[' ']) act();

    // Hunger und Gesundheit
    hunger = Math.max(0, hunger - 0.7 * dt);
    const cold = darkness > 0.45 && !warm;
    let dmg = 0, heal = 0;
    if (hunger <= 0) dmg += 1.5;
    if (cold) dmg += 1.5;
    if (dmg === 0 && hunger > 20) heal = warm ? 3 : 0.6;
    health = Math.min(100, health + (heal - dmg) * dt);
    if (health <= 0) { health = 0; end('over'); return; }

    // Status
    let status = '';
    if (hunger <= 0) status = 'Du hast Hunger. Iss Beeren (F).';
    else if (cold) status = 'Es ist kalt. Geh ans Feuer oder in die Hütte.';
    else if (darkness > 0.45 && warm) status = 'Hier bist du warm.';
    ui.status.textContent = status;

    // Kamera
    const k = Math.min(1, dt * 8);
    camX += (player.x - viewW / 2 - camX) * k;
    camY += (player.y - viewH / 2 - camY) * k;
  }

  function updateHud() {
    ui.health.style.width = health + '%';
    ui.hunger.style.width = hunger + '%';
    ui.day.textContent = `Tag ${Math.min(day, WIN_DAY - 1)} von ${WIN_DAY - 1}`;
    ui.phase.textContent = darkness > 0.5 ? 'Nacht' : darkness > 0.1 ? 'Dämmerung' : 'Tag';
    ui.wood.textContent = inv.wood;
    ui.stone.textContent = inv.stone;
    ui.berries.textContent = inv.berries;
    ui.axe.classList.toggle('hidden', !hasAxe);
    craftButtons.forEach(b => {
      const id = b.dataset.craft;
      const small = b.querySelector('small');
      let off = false;
      if (id) {
        const built = (id === 'axe' && hasAxe) || (id === 'hut' && hut);
        small.textContent = built ? 'Schon gebaut' : b.dataset.label;
        off = built || !canAfford(RECIPES[id]);
      } else {
        off = inv.berries < 1;
      }
      b.classList.toggle('disabled', off);
    });
  }

  // ---------- Zeichnen ----------
  function shadow(x, y, rx, ry) {
    ctx.fillStyle = 'rgba(0,0,0,0.2)';
    ctx.beginPath(); ctx.ellipse(x, y, rx, ry, 0, 0, Math.PI * 2); ctx.fill();
  }
  function circle(x, y, r, color) {
    ctx.fillStyle = color;
    ctx.beginPath(); ctx.arc(x, y, r, 0, Math.PI * 2); ctx.fill();
  }

  function drawTiles() {
    const x0 = Math.max(0, Math.floor(camX / TILE)), x1 = Math.min(W - 1, Math.ceil((camX + viewW) / TILE));
    const y0 = Math.max(0, Math.floor(camY / TILE)), y1 = Math.min(H - 1, Math.ceil((camY + viewH) / TILE));
    const grass = ['#5a9a4e', '#559549', '#609f53'];
    const sand = ['#ecd9a8', '#e6d09c'];
    for (let y = y0; y <= y1; y++) {
      for (let x = x0; x <= x1; x++) {
        const t = world[y][x], h = hash(x, y);
        const sx = x * TILE - camX, sy = y * TILE - camY;
        if (t === 0) {
          ctx.fillStyle = shallow[y][x] ? '#2f8b97' : '#1f6f7e';
          ctx.fillRect(sx, sy, TILE + 1, TILE + 1);
          if (h > 0.75) {
            ctx.strokeStyle = `rgba(255,255,255,${0.12 + 0.12 * Math.sin(time * 1.6 + h * 20)})`;
            ctx.lineWidth = 1.5;
            ctx.beginPath(); ctx.moveTo(sx + 6, sy + 16); ctx.lineTo(sx + 20, sy + 16); ctx.stroke();
          }
        } else if (t === 1) {
          ctx.fillStyle = sand[h > 0.5 ? 1 : 0];
          ctx.fillRect(sx, sy, TILE + 1, TILE + 1);
          if (h > 0.8) { ctx.fillStyle = '#d9c48d'; ctx.fillRect(sx + h * 20, sy + 10, 3, 2); }
        } else {
          ctx.fillStyle = grass[Math.floor(h * 3) % 3];
          ctx.fillRect(sx, sy, TILE + 1, TILE + 1);
          if (h > 0.7) {
            ctx.strokeStyle = '#4a8640'; ctx.lineWidth = 1.5;
            ctx.beginPath();
            ctx.moveTo(sx + 8, sy + 22); ctx.lineTo(sx + 9, sy + 17);
            ctx.moveTo(sx + 12, sy + 22); ctx.lineTo(sx + 12, sy + 16);
            ctx.stroke();
          }
        }
      }
    }
  }

  function drawObject(o) {
    const sway = o.shake > 0 ? Math.sin(time * 60) * o.shake * 8 : 0;
    const x = o.x - camX, y = o.y - camY;
    if (o.type === 'tree') {
      if (o.state === 'empty') {
        shadow(x, y + 8, 8, 3);
        ctx.fillStyle = '#6b4a2f'; ctx.fillRect(x - 5, y + 2, 10, 7);
        ctx.fillStyle = '#a9835a'; ctx.fillRect(x - 5, y + 2, 10, 3);
        return;
      }
      shadow(x, y + 11, 16, 6);
      ctx.fillStyle = '#6b4a2f'; ctx.fillRect(x - 4, y - 2, 8, 14);
      circle(x + sway, y - 14, 16, '#2f7d3e');
      circle(x - 9 + sway, y - 6, 11, '#378a46');
      circle(x + 9 + sway, y - 6, 11, '#2a6f38');
      circle(x - 4 + sway, y - 18, 6, '#4aa157');
    } else if (o.type === 'rock') {
      if (o.state === 'empty') return;
      shadow(x, y + 9, 14, 5);
      ctx.fillStyle = '#7d848a';
      ctx.beginPath();
      ctx.moveTo(x - 12 + sway, y + 8); ctx.lineTo(x - 9 + sway, y - 6); ctx.lineTo(x + 2 + sway, y - 11);
      ctx.lineTo(x + 12 + sway, y - 3); ctx.lineTo(x + 13 + sway, y + 8); ctx.closePath(); ctx.fill();
      ctx.fillStyle = '#a3abb1';
      ctx.beginPath();
      ctx.moveTo(x - 9 + sway, y - 6); ctx.lineTo(x + 2 + sway, y - 11); ctx.lineTo(x + 5 + sway, y - 3); ctx.lineTo(x - 6 + sway, y); ctx.closePath(); ctx.fill();
    } else {
      shadow(x, y + 8, 13, 4);
      const full = o.state === 'full';
      const c = full ? '#3f8f4a' : '#4f8a45';
      circle(x - 6 + sway, y, 8, c); circle(x + 6 + sway, y, 8, c); circle(x + sway, y - 5, 9, full ? '#4aa157' : '#58934d');
      if (full) {
        circle(x - 5 + sway, y - 1, 2.2, '#d1403a'); circle(x + 5 + sway, y + 1, 2.2, '#d1403a'); circle(x + sway, y - 7, 2.2, '#d1403a');
      }
    }
  }

  function drawFire(f) {
    const x = f.x - camX, y = f.y - camY;
    shadow(x, y + 5, 14, 5);
    ctx.save(); ctx.translate(x, y + 3);
    ctx.fillStyle = '#5a3a24';
    ctx.rotate(0.35); ctx.fillRect(-12, -2, 24, 5);
    ctx.rotate(-0.7); ctx.fillRect(-12, -2, 24, 5);
    ctx.restore();
    if (f.fuel > 0) {
      const fl = Math.sin(time * 18 + f.x) * 2 + Math.sin(time * 11) * 1.5;
      ctx.fillStyle = '#f08a3c';
      ctx.beginPath(); ctx.moveTo(x - 8, y + 2); ctx.quadraticCurveTo(x - 7, y - 12, x + fl * 0.4, y - 22 - fl);
      ctx.quadraticCurveTo(x + 8, y - 12, x + 8, y + 2); ctx.closePath(); ctx.fill();
      ctx.fillStyle = '#ffd36b';
      ctx.beginPath(); ctx.moveTo(x - 4, y + 2); ctx.quadraticCurveTo(x - 4, y - 7, x, y - 14 - fl * 0.5);
      ctx.quadraticCurveTo(x + 4, y - 7, x + 4, y + 2); ctx.closePath(); ctx.fill();
      ctx.fillStyle = 'rgba(255,255,255,0.25)'; ctx.fillRect(x - 12, y + 10, 24, 3);
      ctx.fillStyle = '#f08a3c'; ctx.fillRect(x - 12, y + 10, 24 * (f.fuel / FIRE_MAX), 3);
    } else {
      circle(x, y, 5, '#4a4a4a');
    }
  }

  function drawHut(h) {
    const x = h.x - camX, y = h.y - camY;
    shadow(x, y + 10, 26, 7);
    ctx.fillStyle = '#b98b57'; ctx.fillRect(x - 18, y - 14, 36, 24);
    ctx.strokeStyle = '#9a7144'; ctx.lineWidth = 1;
    for (let i = -12; i < 18; i += 8) { ctx.beginPath(); ctx.moveTo(x + i, y - 14); ctx.lineTo(x + i, y + 10); ctx.stroke(); }
    ctx.fillStyle = '#7a3f2a';
    ctx.beginPath(); ctx.moveTo(x - 25, y - 11); ctx.lineTo(x, y - 36); ctx.lineTo(x + 25, y - 11); ctx.closePath(); ctx.fill();
    ctx.fillStyle = '#3a2416'; ctx.fillRect(x - 5, y - 2, 10, 12);
  }

  function drawPlayer() {
    const x = player.x - camX;
    const bob = player.moving ? Math.sin(time * 14) * 1.5 : 0;
    const y = player.y - camY + bob;
    shadow(player.x - camX, player.y - camY + 9, 8, 3);
    ctx.fillStyle = '#3a4a6b'; ctx.fillRect(x - 5, y + 2, 4, 8); ctx.fillRect(x + 1, y + 2, 4, 8);
    ctx.fillStyle = '#e0873a'; ctx.fillRect(x - 6, y - 8, 12, 12);
    circle(x, y - 14, 6, '#f1c79a');
    ctx.fillStyle = '#4a2f1d'; ctx.fillRect(x - 6, y - 21, 12, 5);
    ctx.fillStyle = '#17262b'; ctx.fillRect(x + player.face * 2 - 1, y - 14, 2, 2);
    if (hasAxe) {
      ctx.strokeStyle = '#6b4a2f'; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.moveTo(x + player.face * 8, y + 2); ctx.lineTo(x + player.face * 8, y - 10); ctx.stroke();
      ctx.fillStyle = '#a3abb1'; ctx.fillRect(x + player.face * 8 - (player.face > 0 ? 0 : 5), y - 12, 5, 5);
    }
  }

  function light(c, x, y, r, strength) {
    const g = c.createRadialGradient(x, y, r * 0.15, x, y, r);
    g.addColorStop(0, `rgba(0,0,0,${strength})`);
    g.addColorStop(1, 'rgba(0,0,0,0)');
    c.fillStyle = g;
    c.fillRect(x - r, y - r, r * 2, r * 2);
  }

  function drawNight(s) {
    dctx.setTransform(1, 0, 0, 1, 0, 0);
    dctx.globalCompositeOperation = 'source-over';
    dctx.clearRect(0, 0, dark.width, dark.height);
    dctx.fillStyle = `rgba(6,10,38,${darkness * 0.86})`;
    dctx.fillRect(0, 0, dark.width, dark.height);
    dctx.setTransform(s, 0, 0, s, 0, 0);
    dctx.globalCompositeOperation = 'destination-out';
    light(dctx, player.x - camX, player.y - camY, 70, 0.55);
    for (const f of fires) if (f.fuel > 0) light(dctx, f.x - camX, f.y - camY, 150 + Math.sin(time * 9 + f.x) * 6, 1);
    if (hut) light(dctx, hut.x - camX, hut.y - camY - 6, 90, 0.8);
    dctx.globalCompositeOperation = 'source-over';

    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.drawImage(dark, 0, 0);
    ctx.setTransform(s, 0, 0, s, 0, 0);
    for (const f of fires) {
      if (f.fuel <= 0) continue;
      const x = f.x - camX, y = f.y - camY - 6;
      const g = ctx.createRadialGradient(x, y, 4, x, y, 120);
      g.addColorStop(0, `rgba(255,150,50,${0.28 * darkness})`);
      g.addColorStop(1, 'rgba(255,150,50,0)');
      ctx.fillStyle = g; ctx.fillRect(x - 120, y - 120, 240, 240);
    }
  }

  function draw() {
    const s = dpr * ZOOM;
    ctx.setTransform(s, 0, 0, s, 0, 0);
    ctx.fillStyle = '#1b5e6b';
    ctx.fillRect(0, 0, viewW, viewH);
    drawTiles();

    const items = [];
    for (const o of objects) {
      if (o.x > camX - 50 && o.x < camX + viewW + 50 && o.y > camY - 50 && o.y < camY + viewH + 60) items.push({ y: o.y, f: () => drawObject(o) });
    }
    for (const f of fires) items.push({ y: f.y, f: () => drawFire(f) });
    if (hut) items.push({ y: hut.y, f: () => drawHut(hut) });
    items.push({ y: player.y, f: drawPlayer });
    items.sort((a, b) => a.y - b.y);
    items.forEach(i => i.f());

    if (state === 'play' && target) {
      const x = target.x - camX, y = target.y - camY;
      circle(x, y, 9, 'rgba(23,38,43,0.85)');
      ctx.fillStyle = '#f4ecd6'; ctx.font = 'bold 11px sans-serif';
      ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
      ctx.fillText('E', x, y + 0.5);
    }

    if (darkness > 0.01) drawNight(s);
  }

  // ---------- Eingabe ----------
  window.addEventListener('keydown', e => {
    const k = e.key.toLowerCase();
    if ([' ', 'arrowup', 'arrowdown', 'arrowleft', 'arrowright'].includes(k)) e.preventDefault();
    keys[k] = true;
    if (e.repeat) return;
    if (state === 'play') {
      if (k === '1') craft('axe');
      if (k === '2') craft('fire');
      if (k === '3') craft('hut');
      if (k === 'f') eat();
    } else if (k === 'enter' || k === 'r') {
      startGame();
    }
  });
  window.addEventListener('keyup', e => { keys[e.key.toLowerCase()] = false; });
  window.addEventListener('blur', () => { for (const k in keys) keys[k] = false; });
  canvas.addEventListener('mousedown', act);
  ui.start.addEventListener('click', startGame);
  craftButtons.forEach(b => b.addEventListener('click', () => {
    if (b.dataset.craft) craft(b.dataset.craft); else eat();
    b.blur();
  }));

  // ---------- Start ----------
  newGame();
  let last = performance.now();
  function loop(now) {
    const dt = Math.min(0.05, (now - last) / 1000);
    last = now;
    update(dt);
    updateHud();
    draw();
    requestAnimationFrame(loop);
  }
  requestAnimationFrame(loop);
})();
