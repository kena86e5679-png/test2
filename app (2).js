// ==========================================================
// 空間偏好 AR：視野版（手機網頁）
//
// 後鏡頭拍到的真實空間 → 套用遊戲裡的視野規則：
//   中央區清晰；中央區邊緣是逐級縮小、機率遞減的清晰方塊；
//   外圍全黑，只留下白色小圓點（依邊緣與亮度）與空心方框標記。
// 手機的方向感測器決定視線；走路步伐（加速度計）或「按住前進」決定位置。
// 依你的移動習慣，在眼前生成白色線條構成的虛擬建築（單位：公尺）。
// ==========================================================
(() => {
'use strict';

const DEG = Math.PI / 180;
const $ = (id) => document.getElementById(id);
const clamp01 = (v) => (v < 0 ? 0 : v > 1 ? 1 : v);
const lerp = (a, b, t) => a + (b - a) * t;
const rand = (a, b) => a + Math.random() * (b - a);

// ---------- 畫布 ----------
const cv = $('view');
const ctx = cv.getContext('2d');
const scene = document.createElement('canvas'); // 鏡頭影像 + 虛擬建築
const sctx = scene.getContext('2d');
const sm = document.createElement('canvas'); // 低解析度副本，供分析用
const smctx = sm.getContext('2d', { willReadFrequently: true });
const video = $('cam');

let W = 0, H = 0, DPR = 1, U = 1;
const SAMPLE = 5;
let AW = 0, AH = 0;
let gray = new Float32Array(1);
let edgeMag = new Float32Array(1);
let bandEdge = [0], BAND_TOTAL = 1;

// ---------- 設定 ----------
const S = {
  sizeMul: 1, // 中央區大小倍率
  fovLong: 65, // 相機長邊視角（度）
  stepLen: 0.7, // 一步的長度（公尺）
  dotThreshold: 14,
  dotDensity: 4,
  dotMin: 0.7,
  dotMax: 1.6,
  dotFalloff: 320,
  markerCount: 18,
  bandCell: [25, 12.5, 6.25],
  bandWidth: [50, 37.5, 25],
  bandPow: 1.4,
  limitOn: true,
  showHud: true,
};
// 遊戲裡的中央區（左右各 50°、上 50°、下 58°）在 1000×675 畫面上的比例
const CEN_X = 0.2064; // 半寬 / 畫面寬
const CEN_UP = 0.3058; // 上緣到中心 / 畫面高
const CEN_DOWN = 0.4107; // 下緣到中心 / 畫面高

function loadSettings() {
  try {
    const raw = localStorage.getItem('arVision.v1');
    if (raw) Object.assign(S, JSON.parse(raw));
  } catch (e) { /* 沒有儲存空間也沒關係 */ }
}
function saveSettings() {
  try { localStorage.setItem('arVision.v1', JSON.stringify({ sizeMul: S.sizeMul, fovLong: S.fovLong, stepLen: S.stepLen, dotThreshold: S.dotThreshold, showHud: S.showHud })); } catch (e) { /* ignore */ }
}

// ==========================================================
// 狀態
// ==========================================================
let running = false;
let C = { l: 0, r: 0, t: 0, b: 0 };
const EYE = 1.5; // 眼睛離地（公尺）
const pos = { x: 0, z: 0 };
let pending = 0; // 還沒走完的距離（公尺）
let moveSpeed = 0; // 實際移動速度（公尺/秒）
let steps = 0;
let holdWalk = false;
let lastT = 0;
let timeSinceStart = 0;

// 視線基底（遊戲座標：x 右、y 上、z 朝後；起始朝 -z）
let B = { sr: [1, 0, 0], su: [0, 1, 0], F: [0, 0, -1] };
let FPX = 600; // 焦距（像素）
let hasSensor = false;
let sensor = { a: 0, b: 90, g: 0, seen: false };
let h0 = null; // 校準時的羅盤方位（弧度）
let yawM = 0, pitchM = 0; // 沒有感測器時用拖曳轉動
let headX = 0, headZ = -1; // 水平朝向（單位向量）
let prevYaw = 0;

// ==========================================================
// 尺寸
// ==========================================================
function resize() {
  DPR = Math.min(window.devicePixelRatio || 1, 2);
  W = Math.max(200, window.innerWidth);
  H = Math.max(200, window.innerHeight);
  for (const c of [cv, scene]) {
    c.width = Math.round(W * DPR);
    c.height = Math.round(H * DPR);
  }
  cv.style.width = W + 'px';
  cv.style.height = H + 'px';
  AW = Math.ceil(W / SAMPLE);
  AH = Math.ceil(H / SAMPLE);
  sm.width = AW;
  sm.height = AH;
  gray = new Float32Array(AW * AH);
  edgeMag = new Float32Array(AW * AH);
  U = Math.min(1.1, Math.max(0.55, Math.min(W, H) / 560));
  bandEdge = [0];
  for (let i = 0; i < S.bandWidth.length; i++) bandEdge.push(bandEdge[i] + S.bandWidth[i] * U);
  BAND_TOTAL = bandEdge[bandEdge.length - 1];
  C = centerRect();
}
window.addEventListener('resize', resize);
window.addEventListener('orientationchange', () => setTimeout(resize, 200));

// ==========================================================
// 感測器
// ==========================================================
function screenAngle() {
  let a = 0;
  if (screen.orientation && typeof screen.orientation.angle === 'number') a = screen.orientation.angle;
  else if (typeof window.orientation === 'number') a = window.orientation;
  return ((a % 360) + 360) % 360;
}

function e2g(v) {
  // 地球座標（東、北、上）→ 遊戲座標，起始朝向（h0）對應遊戲的 -z
  const h = Math.atan2(v[0], v[1]);
  const th = h - h0;
  const rho = Math.hypot(v[0], v[1]);
  return [rho * Math.sin(th), v[2], -rho * Math.cos(th)];
}

function sensorBasis() {
  const x = sensor.b * DEG, y = sensor.g * DEG, z = sensor.a * DEG;
  const cX = Math.cos(x), cY = Math.cos(y), cZ = Math.cos(z);
  const sX = Math.sin(x), sY = Math.sin(y), sZ = Math.sin(z);
  const m11 = cZ * cY - sZ * sX * sY, m12 = -cX * sZ, m13 = cY * sZ * sX + cZ * sY;
  const m21 = cY * sZ + cZ * sX * sY, m22 = cZ * cX, m23 = sZ * sY - cZ * cY * sX;
  const m31 = -cX * sY, m32 = sX, m33 = cX * cY;
  const Re = [m11, m21, m31]; // 螢幕右（直立持機）
  const Ue = [m12, m22, m32]; // 螢幕上
  const Fe = [-m13, -m23, -m33]; // 後鏡頭朝向
  if (h0 === null) {
    const hf = Math.hypot(Fe[0], Fe[1]) > 0.3 ? Fe : Ue;
    h0 = Math.atan2(hf[0], hf[1]);
  }
  let r = e2g(Re), u = e2g(Ue);
  const f = e2g(Fe);
  // 螢幕旋轉（橫放）修正
  const ang = screenAngle();
  let sr = r, su = u;
  if (ang === 90) { sr = u.map((q) => -q); su = r; }
  else if (ang === 180) { sr = r.map((q) => -q); su = u.map((q) => -q); }
  else if (ang === 270) { sr = u; su = r.map((q) => -q); }
  return { sr, su, F: f, up: u };
}

function manualBasis() {
  const cy = Math.cos(yawM), sy = Math.sin(yawM), cp = Math.cos(pitchM), sp = Math.sin(pitchM);
  return {
    sr: [cy, 0, sy],
    su: [-sy * sp, cp, cy * sp],
    F: [sy * cp, sp, -cy * cp],
    up: [-sy * sp, cp, cy * sp],
  };
}

function updateCamera() {
  const nb = hasSensor && sensor.seen ? sensorBasis() : manualBasis();
  B = nb;
  // 水平朝向：看地面或天花板時改用手機「上緣」的方向
  let hx = nb.F[0], hz = nb.F[2];
  let hl = Math.hypot(hx, hz);
  if (hl < 0.35) {
    const s = nb.F[1] < 0 ? 1 : -1;
    hx = nb.up[0] * s;
    hz = nb.up[2] * s;
    hl = Math.hypot(hx, hz);
  }
  if (hl > 1e-4) {
    headX = hx / hl;
    headZ = hz / hl;
  }
}

function dot3(a, b) { return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]; }

// 世界點（相對於眼睛的向量）→ 相機座標
function toCam(vx, vy, vz) {
  const v = [vx, vy, vz];
  return [dot3(v, B.sr), dot3(v, B.su), dot3(v, B.F)];
}
function toScreen(c) {
  return [W / 2 + (FPX * c[0]) / c[2], H / 2 - (FPX * c[1]) / c[2]];
}

// ==========================================================
// 視野：中央區與動態縮放
// ==========================================================
const fov = { l: 1, r: 1, u: 1, d: 1, move: 0, prox: { l: 0, r: 0, f: 0 } };
const FOV_MIN = 0.3, MOVE_SHRINK = 0.3, SIDE_SHRINK = 0.6, FRONT_SHRINK = 0.35;
const COVER_RANGE = 3.0; // 公尺
const FOV_IN = 0.2, FOV_OUT = 0.06;

function centerRect() {
  const k = S.sizeMul;
  const kx = k * (W < H ? 1.3 : 1); // 直立時畫面較窄，水平方向多給一些
  return {
    l: Math.max(0, W / 2 - CEN_X * W * kx * fov.l),
    r: Math.min(W, W / 2 + CEN_X * W * kx * fov.r),
    t: Math.max(0, H / 2 - CEN_UP * H * k * fov.u),
    b: Math.min(H, H / 2 + CEN_DOWN * H * k * fov.d),
  };
}

function rectDist(x, y) {
  const dx = Math.max(C.l - x, 0, x - C.r);
  const dy = Math.max(C.t - y, 0, y - C.b);
  return Math.max(dx, dy);
}

function rayHitBox(ox, oz, dx, dz, o, pad) {
  let t0 = 0, t1 = COVER_RANGE;
  const lo = [o.x - o.w / 2 - pad, o.z - o.d / 2 - pad];
  const hi = [o.x + o.w / 2 + pad, o.z + o.d / 2 + pad];
  const org = [ox, oz], dir = [dx, dz];
  for (let k = 0; k < 2; k++) {
    if (Math.abs(dir[k]) < 1e-9) {
      if (org[k] < lo[k] || org[k] > hi[k]) return Infinity;
    } else {
      let a = (lo[k] - org[k]) / dir[k];
      let b = (hi[k] - org[k]) / dir[k];
      if (a > b) { const t = a; a = b; b = t; }
      t0 = Math.max(t0, a);
      t1 = Math.min(t1, b);
      if (t0 > t1) return Infinity;
    }
  }
  return t0;
}

function coverDist(angRad) {
  const fx = headX, fz = headZ;
  const rx = -headZ, rz = headX; // 右手邊（俯視，x 右、z 向後）
  const c = Math.cos(angRad), sn = Math.sin(angRad);
  const dx = fx * c + rx * sn, dz = fz * c + rz * sn;
  let best = COVER_RANGE;
  for (const o of obs) {
    if (o.h < 0.8 || o.dying) continue; // 太矮的不算掩體
    if (Math.abs(o.x - pos.x) > COVER_RANGE + o.w / 2 + 0.5 || Math.abs(o.z - pos.z) > COVER_RANGE + o.d / 2 + 0.5) continue;
    const hit = rayHitBox(pos.x, pos.z, dx, dz, o, 0.3);
    if (hit < best) best = hit;
  }
  return best;
}

function coverProx(list) {
  let best = 0;
  for (const it of list) {
    const q = clamp01(1 - coverDist(it[0] * DEG) / COVER_RANGE);
    best = Math.max(best, it[1] * q * q * (3 - 2 * q));
  }
  return best;
}

function updateVision() {
  const tgt = { l: 1, r: 1, u: 1, d: 1 };
  if (running) {
    const m = clamp01(moveSpeed / 1.6);
    const shrink = MOVE_SHRINK * m;
    const pr = coverProx([[40, 0.85], [90, 1], [140, 0.7]]);
    const pl = coverProx([[-40, 0.85], [-90, 1], [-140, 0.7]]);
    const pf = coverProx([[0, 1], [-20, 0.8], [20, 0.8]]);
    fov.move = m; fov.prox.l = pl; fov.prox.r = pr; fov.prox.f = pf;
    tgt.l = (1 - shrink) * (1 - SIDE_SHRINK * pl);
    tgt.r = (1 - shrink) * (1 - SIDE_SHRINK * pr);
    tgt.u = (1 - shrink) * (1 - FRONT_SHRINK * pf);
    tgt.d = tgt.u;
  } else {
    fov.move = 0; fov.prox.l = fov.prox.r = fov.prox.f = 0;
  }
  for (const k of ['l', 'r', 'u', 'd']) {
    const goal = Math.max(FOV_MIN, tgt[k]);
    fov[k] = lerp(fov[k], goal, goal < fov[k] ? FOV_IN : FOV_OUT);
  }
  C = centerRect();
}

// ==========================================================
// 視野：分析與呈現（與遊戲相同的規則）
// ==========================================================
function hash(a, b, c) {
  let x = Math.imul(a | 0, 73856093) ^ Math.imul(b | 0, 19349663) ^ Math.imul(c | 0, 83492791);
  x = Math.imul(x ^ (x >>> 13), 1274126177);
  x ^= x >>> 16;
  return (x >>> 0) / 4294967296;
}

function analyze() {
  smctx.drawImage(scene, 0, 0, AW, AH);
  const p = smctx.getImageData(0, 0, AW, AH).data;
  for (let k = 0; k < AW * AH; k++) gray[k] = 0.299 * p[4 * k] + 0.587 * p[4 * k + 1] + 0.114 * p[4 * k + 2];
  for (let j = 1; j < AH - 1; j++) {
    for (let i = 1; i < AW - 1; i++) {
      const k = j * AW + i;
      const gx = -gray[k - AW - 1] + gray[k - AW + 1] - 2 * gray[k - 1] + 2 * gray[k + 1] - gray[k + AW - 1] + gray[k + AW + 1];
      const gy = -gray[k - AW - 1] - 2 * gray[k - AW] - gray[k - AW + 1] + gray[k + AW - 1] + 2 * gray[k + AW] + gray[k + AW + 1];
      const m = Math.sqrt(gx * gx + gy * gy) / 4;
      edgeMag[k] = 0.6 * m + 0.4 * edgeMag[k];
    }
  }
}

function blit(x, y, w, h) {
  // 把場景畫布的一塊（CSS 像素座標）畫到主畫布同樣的位置
  if (w <= 0 || h <= 0) return;
  ctx.drawImage(scene, x * DPR, y * DPR, w * DPR, h * DPR, x, y, w, h);
}

function drawDots() {
  const thr = S.dotThreshold;
  const buckets = [[], [], []];
  const ud = Math.min(1.3, Math.max(0.85, U * 1.4));
  const radii = [S.dotMin * ud, ((S.dotMin + S.dotMax) / 2) * ud, S.dotMax * ud];
  for (let j = 0; j < AH; j++) {
    for (let i = 0; i < AW; i++) {
      const k = j * AW + i;
      const x = i * SAMPLE + SAMPLE / 2, y = j * SAMPLE + SAMPLE / 2;
      const d = rectDist(x, y);
      if (d <= 0) continue;
      const edgeN = clamp01((edgeMag[k] - thr * 0.5) / (thr * 3.5));
      const lumN = Math.pow(gray[k] / 255, 2.2) * 0.3;
      const v = Math.max(edgeN, lumN);
      if (v <= 0.02) continue;
      const prox = 0.3 + 0.7 * (1 - Math.min(1, d / (S.dotFalloff * U)));
      const n = Math.floor(v * prox * S.dotDensity + hash(i, j, 0));
      if (n <= 0) continue;
      const b = edgeN > 0.66 ? 2 : edgeN > 0.33 ? 1 : 0;
      for (let q = 0; q < n; q++) {
        buckets[b].push(x + (hash(i, j, q + 1) - 0.5) * SAMPLE, y + (hash(i, j, q + 11) - 0.5) * SAMPLE);
      }
    }
  }
  ctx.save();
  ctx.fillStyle = 'rgba(255,255,255,0.92)';
  for (let b = 0; b < 3; b++) {
    const pts = buckets[b], r = radii[b];
    ctx.beginPath();
    for (let q = 0; q < pts.length; q += 2) {
      ctx.moveTo(pts[q] + r, pts[q + 1]);
      ctx.arc(pts[q], pts[q + 1], r, 0, Math.PI * 2);
    }
    ctx.fill();
  }
  ctx.restore();
}

function drawBand() {
  for (let L = 0; L < S.bandCell.length; L++) {
    const s = S.bandCell[L] * U;
    const d0 = bandEdge[L], d1 = bandEdge[L + 1];
    const kx0 = Math.floor((0 - C.l) / s) - 1, kx1 = Math.ceil((W - C.l) / s) + 1;
    const ky0 = Math.floor((0 - C.t) / s) - 1, ky1 = Math.ceil((H - C.t) / s) + 1;
    for (let ky = ky0; ky <= ky1; ky++) {
      for (let kx = kx0; kx <= kx1; kx++) {
        const x0 = C.l + kx * s, y0 = C.t + ky * s;
        const cx = x0 + s / 2, cy = y0 + s / 2;
        if (cx < 0 || cx > W || cy < 0 || cy > H) continue;
        const d = rectDist(cx, cy);
        if (d <= d0 || d > d1) continue;
        const p = Math.pow(1 - d / BAND_TOTAL, S.bandPow);
        if (hash(kx, ky, L + 50) > p) continue;
        blit(x0, y0, s, s);
      }
    }
  }
}

function drawMarkers() {
  const thr = S.dotThreshold * 2.2;
  const R = 3;
  const cand = [];
  for (let j = R; j < AH - R; j++) {
    for (let i = R; i < AW - R; i++) {
      const m = edgeMag[j * AW + i];
      if (m < thr) continue;
      const x = i * SAMPLE + SAMPLE / 2, y = j * SAMPLE + SAMPLE / 2;
      if (rectDist(x, y) <= 0) continue;
      let isMax = true;
      for (let jj = -R; jj <= R && isMax; jj++) {
        for (let ii = -R; ii <= R; ii++) {
          if (edgeMag[(j + jj) * AW + i + ii] > m) { isMax = false; break; }
        }
      }
      if (isMax) cand.push({ x, y, m, i, j });
    }
  }
  cand.sort((p1, p2) => p2.m - p1.m);
  const n = Math.min(cand.length, S.markerCount);
  ctx.save();
  ctx.strokeStyle = 'rgba(255,255,255,0.9)';
  ctx.lineWidth = 1;
  for (let q = 0; q < n; q++) {
    const c = cand[q];
    const s = (8 + 6 * hash(c.i, c.j, 99)) * Math.max(0.85, U);
    ctx.strokeRect(Math.round(c.x - s / 2) + 0.5, Math.round(c.y - s / 2) + 0.5, s, s);
  }
  ctx.restore();
}

function composeLimited() {
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.fillStyle = '#000';
  ctx.fillRect(0, 0, W, H);
  analyze();
  drawDots();
  drawBand();
  blit(C.l, C.t, C.r - C.l, C.b - C.t);
  drawMarkers();
}

// ==========================================================
// 場景：鏡頭影像 + 虛擬建築（白色線條）
// ==========================================================
function drawVideo() {
  sctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  const vw = video.videoWidth, vh = video.videoHeight;
  if (vw && vh && video.readyState >= 2) {
    const s = Math.max(W / vw, H / vh);
    const dw = vw * s, dh = vh * s;
    sctx.drawImage(video, (W - dw) / 2, (H - dh) / 2, dw, dh);
    FPX = (s * (Math.max(vw, vh) / 2)) / Math.tan((S.fovLong * DEG) / 2);
  } else {
    sctx.fillStyle = '#1b1d22';
    sctx.fillRect(0, 0, W, H);
    FPX = (Math.max(W, H) / 2) / Math.tan((S.fovLong * DEG) / 2);
  }
}

function drawStructures(c) {
  const near = 0.15;
  c.lineJoin = 'round';
  for (const o of obs) {
    const dx = o.x - pos.x, dz = o.z - pos.z;
    const dist = Math.hypot(dx, dz);
    if (dist > 24) continue;
    // 粗略的視錐剔除：中心在相機後方很遠就略過
    const cc = toCam(dx, -EYE, dz);
    if (cc[2] < -(o.w + o.d) && dist > 3) continue;

    let g = 1;
    if (o.gen) {
      const t = clamp01((performance.now() - o.born) / 1200);
      g = 1 - (1 - t) * (1 - t);
      if (o.dying) g *= 1 - clamp01((performance.now() - o.dying) / 900);
      if (g <= 0.01) continue;
    }
    const segs = dist < 9 ? o.segsNear : o.segsFar;
    const alpha = Math.max(0.35, 1 - dist / 24);
    c.strokeStyle = `rgba(255,255,255,${alpha.toFixed(2)})`;
    c.lineWidth = dist < 6 ? 2 : 1.4;
    c.beginPath();
    for (let q = 0; q < segs.length; q++) {
      const sg = segs[q];
      let a = toCam(dx + sg[0], sg[1] * g - EYE, dz + sg[2]);
      let b = toCam(dx + sg[3], sg[4] * g - EYE, dz + sg[5]);
      if (a[2] < near && b[2] < near) continue;
      if (a[2] < near) { const t = (near - a[2]) / (b[2] - a[2]); a = [lerp(a[0], b[0], t), lerp(a[1], b[1], t), near]; }
      else if (b[2] < near) { const t = (near - b[2]) / (a[2] - b[2]); b = [lerp(b[0], a[0], t), lerp(b[1], a[1], t), near]; }
      const pa = toScreen(a), pb = toScreen(b);
      c.moveTo(pa[0], pa[1]);
      c.lineTo(pb[0], pb[1]);
    }
    c.stroke();
  }
}

// ==========================================================
// 虛擬建築（單位：公尺）：用白色線條表示結構
// ==========================================================
let obs = [];

// 建築結構的線段（相對於中心）：外框、基座、樓板、柱、窗框
function buildSegs(w, d, h, kind, withWindows) {
  const segs = [];
  const hx = w / 2, hz = d / 2;
  const L = (x1, y1, z1, x2, y2, z2) => segs.push([x1, y1, z1, x2, y2, z2]);
  const rect = (y, ix) => {
    const ax = hx - (ix || 0), az = hz - (ix || 0);
    L(-ax, y, -az, ax, y, -az); L(ax, y, -az, ax, y, az);
    L(ax, y, az, -ax, y, az); L(-ax, y, az, -ax, y, -az);
  };
  rect(0); rect(h);
  L(-hx, 0, -hz, -hx, h, -hz); L(hx, 0, -hz, hx, h, -hz);
  L(hx, 0, hz, hx, h, hz); L(-hx, 0, hz, -hx, h, hz);

  if (kind === 'pillar') {
    rect(0.25, -0.05); rect(h - 0.3, -0.05);
    return segs;
  }
  if (kind === 'low') {
    rect(h - 0.06, 0.05); // 壓頂
    return segs;
  }

  // 牆：基座、樓板、柱、窗
  const plinth = 0.5;
  const ns = Math.max(1, Math.round((h - plinth) / 1.0));
  const storey = (h - plinth) / ns;
  rect(plinth);
  for (let i = 1; i < ns; i++) rect(plinth + i * storey);
  rect(h - 0.12);
  const longX = w >= d;
  const len = longX ? w : d;
  const nb = Math.max(1, Math.round(len / 1.4)); // 開間數
  const cols = [];
  for (let i = 0; i <= nb; i++) cols.push(-len / 2 + (i * len) / nb);
  for (const c0 of cols) {
    if (longX) { L(c0, 0, -hz, c0, h, -hz); L(c0, 0, hz, c0, h, hz); }
    else { L(-hx, 0, c0, -hx, h, c0); L(hx, 0, c0, hx, h, c0); }
  }
  if (withWindows) {
    for (let i = 0; i < nb; i++) {
      const a = cols[i] + 0.18, b = cols[i + 1] - 0.18;
      for (let s = 0; s < ns; s++) {
        const y0 = plinth + s * storey + 0.22, y1 = plinth + (s + 1) * storey - 0.22;
        for (const sd of [-1, 1]) {
          if (longX) {
            const z = sd * hz;
            L(a, y0, z, b, y0, z); L(b, y0, z, b, y1, z); L(b, y1, z, a, y1, z); L(a, y1, z, a, y0, z);
          } else {
            const x = sd * hx;
            L(x, y0, a, x, y0, b); L(x, y0, b, x, y1, b); L(x, y1, b, x, y1, a); L(x, y1, a, x, y0, a);
          }
        }
      }
    }
  }
  return segs;
}

function makeObs(x, z, w, d, h, kind) {
  return {
    x, z, w, d, h, kind,
    gen: false, gid: 0, born: 0, dying: 0,
    segsFar: buildSegs(w, d, h, kind, false),
    segsNear: buildSegs(w, d, h, kind, true),
  };
}

// ==========================================================
// 移動習慣 → 生成
// ==========================================================
const habit = { open: 0, hug: 0, fast: 0, still: 0, turn: 0, hx: 0, hz: 0 };
let genCount = 0, genGid = 0, genHistory = [];
let genLog = { text: '', until: 0 };
let nextGenAt = 0;
const MAX_GEN = 10;
const GEN_INTERVAL = 6000;
const GEN_FIRST = 8000;

function resetHabit() {
  habit.open = habit.hug = habit.fast = habit.still = habit.turn = 0;
  habit.hx = habit.hz = 0;
  genCount = 0; genGid = 0; genHistory = [];
  genLog = { text: '', until: 0 };
}

function updateHabit(dt) {
  const k = Math.min(1, dt / 10); // 約 10 秒的記憶
  const prox = Math.max(fov.prox.l, fov.prox.r);
  const moving = moveSpeed > 0.25;
  habit.open += ((prox < 0.12 ? 1 : 0) - habit.open) * k;
  habit.hug += ((prox > 0.45 ? 1 : 0) - habit.hug) * k;
  habit.still += ((moving ? 0 : 1) - habit.still) * k;
  habit.fast += ((moveSpeed > 1.3 ? 1 : 0) - habit.fast) * k;
  let dyaw = Math.atan2(headX, -headZ) - prevYaw;
  prevYaw = Math.atan2(headX, -headZ);
  if (dyaw > Math.PI) dyaw -= 2 * Math.PI;
  if (dyaw < -Math.PI) dyaw += 2 * Math.PI;
  habit.turn += (Math.max(-1, Math.min(1, dyaw * 12)) - habit.turn) * Math.min(1, dt / 5);
  if (moving) {
    habit.hx += (headX - habit.hx) * Math.min(1, dt * 1.2);
    habit.hz += (headZ - habit.hz) * Math.min(1, dt * 1.2);
  }
}

const GEN_INFO = {
  cover: { name: '掩體群', why: '你多在空曠處' },
  alley: { name: '巷弄', why: '你習慣貼牆走' },
  wall: { name: '長牆', why: '你走得很快' },
  room: { name: '小房間', why: '你常停下來' },
};

function roomSpecs(cx, cz, w, d, h, doors) {
  const T = 0.25, DW = 1.0, out = [];
  const hw = w / 2, hd = d / 2;
  for (const pr of [['n', cz - hd], ['s', cz + hd]]) {
    if (doors.includes(pr[0])) {
      const seg = (w - DW) / 2;
      out.push([cx - DW / 2 - seg / 2, pr[1], seg, T, h], [cx + DW / 2 + seg / 2, pr[1], seg, T, h]);
    } else out.push([cx, pr[1], w, T, h]);
  }
  const len = d - T;
  for (const pr of [['w', cx - hw], ['e', cx + hw]]) {
    if (doors.includes(pr[0])) {
      const seg = (len - DW) / 2;
      out.push([pr[1], cz - DW / 2 - seg / 2, T, seg, h], [pr[1], cz + DW / 2 + seg / 2, T, seg, h]);
    } else out.push([pr[1], cz, T, len, h]);
  }
  return out;
}

// 規格 [x, z, w, d, h, kind]。alongX 決定長軸朝向。
function genSpecs(type, cx, cz, alongX) {
  const loc = [];
  if (type === 'room') {
    return roomSpecs(cx, cz, 3.6, 3.6, 2.6, alongX ? 'ew' : 'ns').map((s) => [s[0], s[1], s[2], s[3], s[4], 'wall']);
  }
  if (type === 'cover') {
    loc.push([-1.1, -0.8, 0.9, 0.9, 1.05, 'low'], [0.9, -0.9, 0.9, 0.9, 1.15, 'low'],
      [-0.8, 1.0, 0.9, 0.9, 1.0, 'low'], [1.2, 0.8, 0.9, 0.9, 0.95, 'low'], [0, 0, 0.4, 0.4, 2.6, 'pillar']);
  } else if (type === 'alley') {
    loc.push([0, -0.925, 5, 0.25, 2.6, 'wall'], [0, 0.925, 5, 0.25, 2.6, 'wall']);
  } else if (type === 'wall') {
    loc.push([-1.7, 0, 2.2, 0.25, 2.6, 'wall'], [1.7, 0, 2.2, 0.25, 2.6, 'wall']);
  }
  return loc.map((q) => (alongX
    ? [cx + q[0], cz + q[1], q[2], q[3], q[4], q[5]]
    : [cx + q[1], cz + q[0], q[3], q[2], q[4], q[5]]));
}

function specsValid(specs) {
  for (const sp of specs) {
    const x = sp[0], z = sp[1], w = sp[2], d = sp[3];
    const pdx = Math.max(Math.abs(pos.x - x) - w / 2, 0);
    const pdz = Math.max(Math.abs(pos.z - z) - d / 2, 0);
    if (Math.hypot(pdx, pdz) < 2.0) return false;
    for (const o of obs) {
      if (Math.abs(x - o.x) < (w + o.w) / 2 + 0.8 && Math.abs(z - o.z) < (d + o.d) / 2 + 0.8) return false;
    }
  }
  return true;
}

function tryPlace(type) {
  let hx = habit.hx, hz = habit.hz;
  let len = Math.hypot(hx, hz);
  if (len < 0.25) { hx = headX; hz = headZ; len = 1; }
  hx /= len; hz /= len;
  const a = habit.turn * 0.5;
  const dirx = hx * Math.cos(a) - hz * Math.sin(a);
  const dirz = hx * Math.sin(a) + hz * Math.cos(a);
  const alongHeading = Math.abs(hx) > Math.abs(hz);
  for (let k = 0; k < 30; k++) {
    const spread = (k / 30) * Math.PI * 0.9;
    const ta = rand(-spread, spread);
    const far = 3.6 + rand(0, 2.2 + k * 0.12);
    const ux = dirx * Math.cos(ta) - dirz * Math.sin(ta);
    const uz = dirx * Math.sin(ta) + dirz * Math.cos(ta);
    const cx = pos.x + ux * far + rand(-0.4, 0.4);
    const cz = pos.z + uz * far + rand(-0.4, 0.4);
    let alongX;
    if (type === 'alley') alongX = alongHeading;
    else if (type === 'wall') alongX = !alongHeading;
    else if (type === 'room') alongX = alongHeading;
    else alongX = Math.random() < 0.5;
    const specs = genSpecs(type, cx, cz, alongX);
    if (!specsValid(specs)) continue;
    genGid++;
    const now = performance.now();
    for (const sp of specs) {
      const o = makeObs(sp[0], sp[1], sp[2], sp[3], sp[4], sp[5]);
      o.gen = true; o.gid = genGid; o.born = now;
      obs.push(o);
    }
    return true;
  }
  return false;
}

function generateByHabit() {
  const scores = {
    cover: habit.open + 0.12,
    alley: habit.hug * 1.2 + 0.05,
    wall: habit.fast * 1.2 + 0.05,
    room: habit.still + 0.1,
  };
  const recent = genHistory.slice(-3);
  const order = Object.keys(scores)
    .map((k) => ({ k, v: scores[k] - 0.2 * recent.filter((r) => r === k).length + rand(0, 0.12) }))
    .sort((p1, p2) => p2.v - p1.v);
  for (const it of order) {
    if (tryPlace(it.k)) {
      genCount++;
      genHistory.push(it.k);
      const info = GEN_INFO[it.k];
      genLog = { text: `生成 #${genCount}：${info.name}（${info.why}）`, until: performance.now() + 5000 };
      pruneOldGen();
      return true;
    }
  }
  return false;
}

function pruneOldGen() {
  const alive = {};
  for (const o of obs) if (o.gen && !o.dying) (alive[o.gid] = alive[o.gid] || []).push(o);
  const ids = Object.keys(alive).map(Number).sort((p1, p2) => p1 - p2);
  const now = performance.now();
  for (const id of ids) {
    if (ids.length <= MAX_GEN) break;
    const far = alive[id].every((o) => Math.hypot(o.x - pos.x, o.z - pos.z) > 10);
    if (!far) continue;
    for (const o of alive[id]) o.dying = now;
    ids.splice(ids.indexOf(id), 1);
  }
}

function updateGeneration(now) {
  if (obs.some((o) => o.dying && now - o.dying > 900)) obs = obs.filter((o) => !(o.dying && now - o.dying > 900));
  if (now >= nextGenAt) {
    generateByHabit();
    nextGenAt = now + GEN_INTERVAL;
  }
}

// ==========================================================
// 移動
// ==========================================================
function updateMove(dt) {
  if (holdWalk) pending = Math.min(pending + 1.3 * dt, 2);
  const mv = Math.min(pending, 2.0 * dt);
  pending -= mv;
  pos.x += headX * mv;
  pos.z += headZ * mv;
  moveSpeed += (mv / Math.max(dt, 1e-3) - moveSpeed) * Math.min(1, dt * 6);
  if (moveSpeed < 0.02) moveSpeed = 0;
}

let accBase = 9.8, prevSig = 0, lastStep = 0;
function onMotion(e) {
  const a = e.accelerationIncludingGravity;
  if (!a || a.x == null) return;
  const mag = Math.hypot(a.x, a.y, a.z);
  accBase += (mag - accBase) * 0.08;
  const sig = mag - accBase;
  const now = performance.now();
  if (sig > 1.3 && prevSig <= 1.3 && now - lastStep > 320) {
    lastStep = now;
    steps++;
    pending += S.stepLen;
  }
  prevSig = sig;
}

function onOrient(e) {
  if (e.beta == null || e.gamma == null) return;
  sensor.a = e.alpha == null ? 0 : e.alpha;
  sensor.b = e.beta;
  sensor.g = e.gamma;
  sensor.seen = true;
  hasSensor = true;
}

// ==========================================================
// 文字（畫在主畫布上）
// ==========================================================
function pct(v) { return Math.round(v * 100) + '%'; }

function drawHud(now) {
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  if (!S.showHud) {
    if (now < genLog.until) hudBox([`> ${genLog.text}`]);
    return;
  }
  const lines = [
    `> 視野 左${pct(fov.l)} 右${pct(fov.r)} 上下${pct(fov.u)}　速度 ${moveSpeed.toFixed(1)} m/s`,
    `> 習慣 空曠${pct(habit.open)} 貼牆${pct(habit.hug)} 快走${pct(habit.fast)} 停留${pct(habit.still)}`,
    `> 虛擬建築 ${new Set(obs.filter((o) => o.gen && !o.dying).map((o) => o.gid)).size} 處　步數 ${steps}${hasSensor ? '' : '　（無方向感測：拖曳轉向）'}`,
  ];
  if (now < genLog.until) lines.push(`> ${genLog.text}`);
  hudBox(lines);
}

function hudBox(lines) {
  const top = 10 + 0; // 安全區域由 CSS 的 viewport-fit 與 env() 處理，這裡留一點邊
  ctx.font = '11px ui-monospace, Menlo, monospace';
  let w = 0;
  for (const t of lines) w = Math.max(w, ctx.measureText(t).width);
  ctx.fillStyle = 'rgba(0,0,0,0.55)';
  ctx.fillRect(8, top - 4, Math.min(W - 16, w + 16), lines.length * 15 + 8);
  ctx.fillStyle = 'rgba(255,255,255,0.92)';
  ctx.textAlign = 'left';
  ctx.textBaseline = 'top';
  lines.forEach((t, i) => ctx.fillText(t, 16, top + i * 15));
}

// ==========================================================
// 主迴圈
// ==========================================================
function frame(t) {
  requestAnimationFrame(frame);
  if (!running) return;
  const dt = Math.min(0.1, Math.max(0.001, (t - lastT) / 1000));
  lastT = t;
  timeSinceStart += dt;

  updateCamera();
  updateMove(dt);
  updateVision();
  updateHabit(dt);
  updateGeneration(performance.now());

  drawVideo();
  drawStructures(sctx);
  if (S.limitOn) {
    composeLimited();
  } else {
    ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
    ctx.drawImage(scene, 0, 0, W, H);
    C = centerRect();
  }
  drawHud(performance.now());
}

// ==========================================================
// 啟動與操作
// ==========================================================
function calibrate() {
  // 把目前手機朝向當作「前方」
  h0 = null;
  yawM = 0;
}

function resetWorld() {
  obs = [];
  pos.x = pos.z = 0;
  pending = 0;
  moveSpeed = 0;
  steps = 0;
  resetHabit();
}

function seedWorld() {
  updateCamera();
  tryPlace('cover');
  genCount++;
  genHistory.push('cover');
  nextGenAt = performance.now() + GEN_FIRST;
}

async function start() {
  const err = $('err');
  err.textContent = '';
  try {
    // iOS 需要在點擊當下要求動作與方向感測的權限
    if (typeof DeviceOrientationEvent !== 'undefined' && typeof DeviceOrientationEvent.requestPermission === 'function') {
      const r = await DeviceOrientationEvent.requestPermission();
      if (r !== 'granted') err.textContent = '沒有取得方向感測權限，將改用拖曳螢幕轉向。';
    }
    if (typeof DeviceMotionEvent !== 'undefined' && typeof DeviceMotionEvent.requestPermission === 'function') {
      try { await DeviceMotionEvent.requestPermission(); } catch (e) { /* 沒有也能用「按住前進」 */ }
    }
  } catch (e) {
    err.textContent = '感測器權限被拒絕，將改用拖曳螢幕轉向。';
  }

  window.addEventListener('deviceorientation', onOrient);
  window.addEventListener('devicemotion', onMotion);

  try {
    if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) throw new Error('此瀏覽器不支援鏡頭（需要 https 網址）');
    const stream = await navigator.mediaDevices.getUserMedia({
      video: { facingMode: { ideal: 'environment' }, width: { ideal: 1280 }, height: { ideal: 720 } },
      audio: false,
    });
    video.srcObject = stream;
    await video.play();
  } catch (e) {
    err.textContent = '無法開啟鏡頭：' + (e && e.message ? e.message : e) + '。可以先用深色背景測試，但看不到真實空間。';
    await new Promise((res) => setTimeout(res, 1800));
  }

  try { if (navigator.wakeLock) await navigator.wakeLock.request('screen'); } catch (e) { /* ignore */ }

  $('intro').style.display = 'none';
  $('bar').hidden = false;
  resize();
  resetWorld();
  calibrate();
  seedWorld();
  running = true;
  lastT = performance.now();
}

function bindUI() {
  $('start').addEventListener('click', start);
  $('bCal').addEventListener('click', calibrate);
  $('bLimit').addEventListener('click', (e) => {
    S.limitOn = !S.limitOn;
    e.currentTarget.classList.toggle('on', S.limitOn);
  });
  const walk = $('bWalk');
  const on = (e) => { e.preventDefault(); holdWalk = true; walk.classList.add('on'); };
  const off = (e) => { e.preventDefault(); holdWalk = false; walk.classList.remove('on'); };
  walk.addEventListener('pointerdown', on);
  walk.addEventListener('pointerup', off);
  walk.addEventListener('pointercancel', off);
  walk.addEventListener('pointerleave', off);
  $('bSet').addEventListener('click', () => $('panel').classList.toggle('open'));

  const bind = (id, out, key, fmt, onChange) => {
    const el = $(id), o = $(out);
    el.value = S[key];
    o.textContent = fmt(S[key]);
    el.addEventListener('input', () => {
      S[key] = parseFloat(el.value);
      o.textContent = fmt(S[key]);
      if (onChange) onChange();
      saveSettings();
    });
  };
  bind('sSize', 'oSize', 'sizeMul', (v) => v.toFixed(2), () => { C = centerRect(); });
  bind('sFov', 'oFov', 'fovLong', (v) => v + '°');
  bind('sStep', 'oStep', 'stepLen', (v) => v.toFixed(2));
  bind('sDot', 'oDot', 'dotThreshold', (v) => String(v));
  const hudBtn = $('bHud');
  hudBtn.classList.toggle('on', S.showHud);
  hudBtn.addEventListener('click', () => { S.showHud = !S.showHud; hudBtn.classList.toggle('on', S.showHud); saveSettings(); });
  $('bClear').addEventListener('click', () => { obs = obs.filter((o) => !o.gen); genCount = 0; genHistory = []; });
  $('bGen').addEventListener('click', () => { generateByHabit(); });

  // 沒有方向感測器時（桌機測試）：拖曳轉向、WASD 前進
  let drag = null;
  cv.addEventListener('pointerdown', (e) => { drag = { x: e.clientX, y: e.clientY }; });
  window.addEventListener('pointerup', () => { drag = null; });
  window.addEventListener('pointermove', (e) => {
    if (!drag || (hasSensor && sensor.seen)) return;
    yawM += (e.clientX - drag.x) * 0.006;
    pitchM = Math.max(-1.3, Math.min(1.3, pitchM - (e.clientY - drag.y) * 0.006));
    drag = { x: e.clientX, y: e.clientY };
  });
  window.addEventListener('keydown', (e) => { if (e.code === 'KeyW') holdWalk = true; });
  window.addEventListener('keyup', (e) => { if (e.code === 'KeyW') holdWalk = false; });
}

loadSettings();
bindUI();
resize();
requestAnimationFrame(frame);

// 供除錯與自動測試使用
window.__ar = { S, fov, habit, get obs() { return obs; }, pos, sensor, tryPlace, generateByHabit, start, calibrate };
})();
