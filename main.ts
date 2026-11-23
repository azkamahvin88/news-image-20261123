// Monday 23 November 2026 — The World in One Day.
// A program that draws a one-page newspaper front page summing up the
// world's news of Monday 23 November 2026 and writes it to /output/entry.png.
// Pure Node 22 standard library. No network, no clock, no randomness:
// two runs write byte-identical PNGs. Text is rendered from a 1-bit glyph
// atlas (atlas.json, generated from system DejaVu/Noto fonts at build time
// and shipped in this repository) with box-filter resampling, so every size
// from 8px footnotes to the 54px masthead stays legible.
// SPDX-License-Identifier: MIT
import { readFileSync, writeFileSync, mkdirSync } from "node:fs";
import { deflateSync } from "node:zlib";

const W = 1024;
const H = 1024;

// ---------------------------------------------------------------- palette
const PAPER = [246, 241, 229];
const INK = [20, 18, 16];
const RED = [158, 27, 27];
const NAVY = [31, 58, 95];
const GRAY = [107, 101, 92];
const RULE = [201, 191, 168];
const LIGHT = [232, 226, 210];
const WHITE = [255, 255, 255];
const BLACK = [17, 17, 17];
const OCHRE = [180, 118, 42];
const GREEN = [46, 107, 52];
const PURPLE = [107, 74, 140];
const TEAL = [42, 122, 122];
const MIDGRAY = [85, 85, 85];

// ---------------------------------------------------------------- canvas
const px = new Uint8Array(W * H * 3);
for (let i = 0; i < W * H; i++) {
  px[i * 3] = PAPER[0]; px[i * 3 + 1] = PAPER[1]; px[i * 3 + 2] = PAPER[2];
}
function blend(x: number, y: number, c: number[], a: number) {
  if (x < 0 || y < 0 || x >= W || y >= H || a <= 0) return;
  if (a > 1) a = 1;
  const o = (y * W + x) * 3;
  px[o] = Math.round(px[o] * (1 - a) + c[0] * a);
  px[o + 1] = Math.round(px[o + 1] * (1 - a) + c[1] * a);
  px[o + 2] = Math.round(px[o + 2] * (1 - a) + c[2] * a);
}
function rect(x: number, y: number, w: number, h: number, c: number[]) {
  x = Math.round(x); y = Math.round(y); w = Math.round(w); h = Math.round(h);
  for (let yy = Math.max(0, y); yy < Math.min(H, y + h); yy++)
    for (let xx = Math.max(0, x); xx < Math.min(W, x + w); xx++) {
      const o = (yy * W + xx) * 3;
      px[o] = c[0]; px[o + 1] = c[1]; px[o + 2] = c[2];
    }
}
function hline(x: number, y: number, w: number, t: number, c: number[]) {
  rect(x, y, w, t, c);
}
function vline(x: number, y: number, h: number, t: number, c: number[]) {
  rect(x, y, t, h, c);
}
function disc(cx: number, cy: number, r: number, c: number[], a = 1) {
  const r2 = r * r;
  for (let y = Math.floor(cy - r); y <= Math.ceil(cy + r); y++)
    for (let x = Math.floor(cx - r); x <= Math.ceil(cx + r); x++) {
      const dx = x + 0.5 - cx, dy = y + 0.5 - cy;
      if (dx * dx + dy * dy <= r2) blend(x, y, c, a);
    }
}
function ring(cx: number, cy: number, r: number, t: number, c: number[]) {
  for (let y = Math.floor(cy - r - 1); y <= Math.ceil(cy + r + 1); y++)
    for (let x = Math.floor(cx - r - 1); x <= Math.ceil(cx + r + 1); x++) {
      const d = Math.hypot(x + 0.5 - cx, y + 0.5 - cy);
      if (d <= r && d >= r - t) blend(x, y, c, 1);
    }
}
function line(x0: number, y0: number, x1: number, y1: number, t: number, c: number[]) {
  const d = Math.hypot(x1 - x0, y1 - y0);
  const n = Math.max(1, Math.ceil(d * 2));
  for (let i = 0; i <= n; i++) {
    const s = i / n;
    disc(x0 + (x1 - x0) * s, y0 + (y1 - y0) * s, t / 2, c);
  }
}
function poly(pts: [number, number][], c: number[], a = 1) {
  let minY = Infinity, maxY = -Infinity;
  for (const p of pts) { minY = Math.min(minY, p[1]); maxY = Math.max(maxY, p[1]); }
  for (let y = Math.floor(minY); y <= Math.ceil(maxY); y++) {
    const xs: number[] = [];
    for (let i = 0; i < pts.length; i++) {
      const a2 = pts[i], b = pts[(i + 1) % pts.length];
      if ((a2[1] <= y + 0.5 && b[1] > y + 0.5) || (b[1] <= y + 0.5 && a2[1] > y + 0.5)) {
        xs.push(a2[0] + ((y + 0.5 - a2[1]) / (b[1] - a2[1])) * (b[0] - a2[0]));
      }
    }
    xs.sort((m, n) => m - n);
    for (let k = 0; k + 1 < xs.length; k += 2)
      for (let x = Math.ceil(xs[k]); x <= Math.floor(xs[k + 1]); x++) blend(x, y, c, a);
  }
}

// ---------------------------------------------------------------- PNG out
const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();
function crc32(buf: Buffer): number {
  let c = 0xffffffff;
  for (let i = 0; i < buf.length; i++) c = CRC_TABLE[(c ^ buf[i]) & 0xff] ^ (c >>> 8);
  return (c ^ 0xffffffff) >>> 0;
}
function chunk(type: string, data: Buffer): Buffer {
  const out = Buffer.alloc(12 + data.length);
  out.writeUInt32BE(data.length, 0);
  out.write(type, 4, "ascii");
  data.copy(out, 8);
  out.writeUInt32BE(crc32(Buffer.concat([Buffer.from(type, "ascii"), data])), 8 + data.length);
  return out;
}
function writePNG(path: string) {
  const raw = Buffer.alloc(H * (1 + W * 3));
  for (let y = 0; y < H; y++) {
    raw[y * (1 + W * 3)] = 0;
    Buffer.from(px.buffer, y * W * 3, W * 3).copy(raw, y * (1 + W * 3) + 1);
  }
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(W, 0); ihdr.writeUInt32BE(H, 4);
  ihdr[8] = 8; ihdr[9] = 2; ihdr[10] = 0; ihdr[11] = 0; ihdr[12] = 0;
  const idat = deflateSync(raw, { level: 9 });
  const png = Buffer.concat([
    Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]),
    chunk("IHDR", ihdr), chunk("IDAT", idat), chunk("IEND", Buffer.alloc(0)),
  ]);
  mkdirSync(path.slice(0, path.lastIndexOf("/")), { recursive: true });
  writeFileSync(path, png);
  return png.length;
}

// ---------------------------------------------------------------- text
type Glyph = { adv: number; xoff: number; yoff: number; w: number; h: number; bits: Uint8Array };
const ATLAS = JSON.parse(readFileSync(new URL("./atlas.json", import.meta.url), "utf8"));
const ATLAS_SIZE = ATLAS.size as number;
const glyphCache = new Map<string, Glyph>();
function getGlyph(font: string, ch: string): Glyph {
  const key = font + "|" + ch;
  let g = glyphCache.get(key);
  if (g) return g;
  const raw = ATLAS.fonts[font][ch] as [number, number, number, number, number, string] | undefined;
  if (!raw) return getGlyph(font, "?");
  const [adv, xoff, yoff, w, h, b64] = raw;
  const bytes = Buffer.from(b64, "base64");
  const bits = new Uint8Array(w * h);
  for (let i = 0; i < w * h; i++) {
    bits[i] = (bytes[i >> 3] >> (7 - (i & 7))) & 1;
  }
  g = { adv, xoff, yoff, w, h, bits };
  glyphCache.set(key, g);
  return g;
}
function textWidth(font: string, text: string, size: number): number {
  const s = size / ATLAS_SIZE;
  let w = 0;
  for (const ch of text) w += getGlyph(font, ch).adv * s;
  return w;
}
// Draw text at baseline (x, y). Returns width drawn.
function drawText(font: string, text: string, x: number, y: number, size: number, c: number[], align: "l" | "c" | "r" = "l"): number {
  const s = size / ATLAS_SIZE;
  const total = textWidth(font, text, size);
  let cx = align === "c" ? x - total / 2 : align === "r" ? x - total : x;
  for (const ch of text) {
    const g = getGlyph(font, ch);
    if (g.w > 0 && g.h > 0) {
      const gx = cx + g.xoff * s;
      const gy = y + g.yoff * s;
      const gw = g.w * s, gh = g.h * s;
      const x0 = Math.max(0, Math.floor(gx)), x1 = Math.min(W - 1, Math.ceil(gx + gw) - 1);
      const y0 = Math.max(0, Math.floor(gy)), y1 = Math.min(H - 1, Math.ceil(gy + gh) - 1);
      for (let py = y0; py <= y1; py++) {
        for (let pxx = x0; pxx <= x1; pxx++) {
          // coverage: fraction of source glyph pixels set inside this dest pixel
          const sx0 = (pxx - gx) / s, sx1 = (pxx + 1 - gx) / s;
          const sy0 = (py - gy) / s, sy1 = (py + 1 - gy) / s;
          const ix0 = Math.max(0, Math.floor(sx0)), ix1 = Math.min(g.w - 1, Math.ceil(sx1) - 1);
          const iy0 = Math.max(0, Math.floor(sy0)), iy1 = Math.min(g.h - 1, Math.ceil(sy1) - 1);
          if (ix1 < ix0 || iy1 < iy0) continue;
          let set = 0, tot = 0;
          for (let iy = iy0; iy <= iy1; iy++) {
            const wy = Math.min(sy1, iy + 1) - Math.max(sy0, iy);
            if (wy <= 0) continue;
            for (let ix = ix0; ix <= ix1; ix++) {
              const wx = Math.min(sx1, ix + 1) - Math.max(sx0, ix);
              if (wx <= 0) continue;
              tot += wx * wy;
              if (g.bits[iy * g.w + ix]) set += wx * wy;
            }
          }
          if (tot > 0 && set > 0) blend(pxx, py, c, set / tot);
        }
      }
    }
    cx += g.adv * s;
  }
  return total;
}
function wrap(font: string, text: string, size: number, maxW: number): string[] {
  const words = text.split(" ");
  const lines: string[] = [];
  let cur = "";
  for (const word of words) {
    const test = cur ? cur + " " + word : word;
    if (textWidth(font, test, size) <= maxW || !cur) cur = test;
    else { lines.push(cur); cur = word; }
  }
  if (cur) lines.push(cur);
  return lines;
}
function drawPara(font: string, text: string, x: number, y: number, size: number, maxW: number, c: number[], lh: number): number {
  const lines = wrap(font, text, size, maxW);
  for (let i = 0; i < lines.length; i++) drawText(font, lines[i], x, y + i * lh, size, c);
  return lines.length;
}

// ---------------------------------------------------------------- content
// Every story below happened, or was first reported, on Monday 23 November
// 2026 (or broke late Sunday 22 Nov and led Monday's editions). Figures and
// sources as reported; unverified claims are marked CLAIM / REPORTED.
const LEADS = [
  {
    n: 1, tag: "COP31 · ANTALYA", art: "globe",
    head: "COP31 COLLAPSES — NO DEAL AFTER RECORD OVERTIME",
    body: "After two weeks of talks and a record 44 hours of overtime, the Antalya summit ended with no pact. The final draft never mentions \u201cfossil fuels\u201d. The EU, UK, Marshall Islands and Panama refused it; Guterres was \u201cdeeply disappointed\u201d.",
    src: "UN News · The Times",
  },
  {
    n: 2, tag: "MARKETS · AI ROUT", art: "chart",
    head: "AI ROUT — MARKETS BRACE FOR MORE SELLING",
    body: "The Nasdaq fell 10% last week, its worst week since the March 2020 panic; Taiwan plunged 17%, its worst since 1990. Futures rebounded about 2% on Monday as Asia braced for more selling. Triggers: a reported SEC probe into Nvidia and a wobbling Anthropic IPO.",
    src: "Reuters",
  },
  {
    n: 3, tag: "UKRAINE · KYIV", art: "shield",
    head: "UKRAINE PLEADS FOR PATRIOT INTERCEPTORS",
    body: "Zelensky urged the US to approve Patriot interceptor deliveries after a week of Russian attacks on 20 regions: about 2,700 drones, 1,460 guided bombs, 165 missiles. A block in Dymer, north of Kyiv, collapsed \u2014 2 dead, 14 missing, including 2 children.",
    src: "Al Jazeera",
  },
];

const SMALL = [
  { n: 4, tag: "INDONESIA", art: "factory",
    head: "FACTORY FIRE: 3 DEAD, ~50 MISSING",
    body: "Fire at the Fonusa candy plant in Cikande since Saturday. 3 dead, ~50 missing; search resumed Monday.",
    src: "AP · Reuters" },
  { n: 5, tag: "SOUTH KOREA", art: "exam",
    head: "MINISTER QUITS OVER EXAM CHEATING",
    body: "Education Minister Choi Kyo-jin quit over AI anti-cheating chaos at the CSAT exam. 111 cases caught.",
    src: "Korea JoongAng Daily" },
  { n: 6, tag: "NEPAL–INDIA", art: "flags",
    head: "NEPAL PM MEETS MODI IN DELHI",
    body: "PM Balendra Shah met PM Modi in Delhi, his first bilateral trip abroad since March. MoUs signed.",
    src: "IANS · ANI" },
  { n: 7, tag: "FOOTBALL", art: "ball",
    head: "LIVERPOOL 4\u20130 MAN UTD",
    body: "Liverpool thrashed 10-man Man Utd 4\u20130 at Anfield \u2014 Pochettino\u2019s first game as boss. Yoro off in minute 8.",
    src: "Reuters" },
  { n: 8, tag: "FORMULA 1", art: "f1",
    head: "VERSTAPPEN WINS CHAOTIC VEGAS GP",
    body: "Verstappen won a Las Vegas GP with 34 lead changes and 300+ overtakes. Norris 2nd, Piastri 3rd.",
    src: "Formula1.com · Sky Sports" },
  { n: 9, tag: "CRICKET", art: "cricket",
    head: "INDIA POST RECORD 720/9 DECLARED",
    body: "India set a record 720/9 declared in the Wellington Test vs New Zealand, day four on Monday.",
    src: "Observer Voice" },
  { n: 10, tag: "GULF", art: "radar",
    head: "GULF ON EDGE AS CLAIMS FLY",
    body: "IRGC CLAIMS it hit 2 Patriot radars at the US base in Bahrain \u2014 UNVERIFIED. Bahrain: intercepted; 2 hurt.",
    src: "AP wire" },
  { n: 11, tag: "MYANMAR", art: "gavel",
    head: "MYANMAR CALLS ASEAN MOVE \u201cUNFAIR\u201d",
    body: "Myanmar called ASEAN\u2019s decision \u201cunfair and imbalanced\u201d. France wants UN Security Council action.",
    src: "Arab News" },
  { n: 12, tag: "PORTUGAL", art: "march",
    head: "THOUSANDS MARCH IN LISBON",
    body: "Thousands marched in Lisbon to protest the soaring cost of living.",
    src: "JagranJosh" },
  { n: 13, tag: "CONGO", art: "virus",
    head: "FIGHTING NEARS EBOLA ZONE, WHO WARNS",
    body: "WHO: fighting near the Congo Ebola outbreak disrupts the response. 11,000+ cases, 5,500+ dead.",
    src: "Arab News · The New Humanitarian" },
];

// Short source tags for the small-story label row (full names stay in the
// lead sources and in the ALSO list).
const SHORT_SRC: Record<number, string> = {
  4: "AP", 5: "KOREA JOONGANG", 6: "IANS · ANI", 7: "REUTERS", 8: "F1.COM",
  9: "OBSERVER", 10: "AP WIRE", 11: "ARAB NEWS", 12: "JAGRANJOSH", 13: "ARAB NEWS",
};

// One line each: number, headline, source. Kept short so each fits its column.
const ALSO: [number, string, string][] = [
  [14, "Russian freighter Sparta II still burning off Finland", "Reuters"],
  [15, "Ukraine hits 2 Russian ships off Benghazi, Libya", "ISW"],
  [16, "UK to build long-range drones for Ukraine", "Ukrainska Pravda"],
  [17, "US Democrats win House majority, 258+ seats", "Arab News"],
  [18, "US seeks answers on Nvidia chip sales to China", "Wire"],
  [19, "New detail: Alice Huang tied to secret chip network", "Daily Jagran"],
  [20, "South Sudan: SPLA-IO attack kills 24 civilians", "Arab News"],
  [21, "South Africa's ANC struggles to form local coalitions", "Briefing"],
  [22, "Poland: Russia 'tried twice to kill' rapper", "Arab News"],
  [23, "Israel minister calls settler violence 'Jewish terrorism'", "Wire"],
  [24, "Pakistan FM hopes for US\u2013Iran deal, warns of long war", "Arab News"],
  [25, "India: Shah launches Rs 4,000-crore Arunachal push", "Observer Voice"],
  [26, "India: BJP MP Ramrao Wadkute dies of heart attack", "Daily Jagran"],
  [27, "IFFI 2026 holds BRICS Roundtable", "JagranJosh"],
  [28, "Anupama keeps IBSF women's snooker world title", "Daily Jagran"],
  [29, "Australia rebukes US budget office over AUKUS remark", "Wire"],
  [30, "US lawmaker threatens SpaceX over Starshield", "CNN"],
  [31, "Swimmer crosses Strait of Hormuz for animals", "Wire"],
  [32, "Yemen army claims 149 Houthis killed or hurt in a day", "Wire"],
  [33, "Saudi Arabia downs drones; Houthis report Sanaa strikes", "Wire"],
  [34, "Ex-PMs May, Cameron, Blair advise Burnham on EU", "Huddleworld"],
  [35, "Jeweller Paolo Bulgari dies aged 89", "Huddleworld"],
];

const STATS: [string, string][] = [
  ["NO DEAL", "COP31 ends with no pact"],
  ["-10%", "Nasdaq's weekly fall"],
  ["~50", "missing in Indonesia fire"],
  ["4\u20130", "Liverpool rout Man Utd"],
  ["111", "CSAT cheating cases caught"],
  ["258", "Democrats' House seats"],
];

// Counted from the 35 stories on this page. Oceania has exactly one story.
const REGIONS: [string, number, number[]][] = [
  ["ASIA", 10, RED],
  ["EUROPE", 9, NAVY],
  ["MIDDLE EAST", 5, OCHRE],
  ["AMERICAS", 4, GREEN],
  ["AFRICA", 3, PURPLE],
  ["GLOBAL", 3, MIDGRAY],
  ["OCEANIA", 1, TEAL],
];

const DATE_CHECK =
  "Dated before 23 Nov, so left out: Kryvyi Rih triple-tap (21 Nov) \u00B7 Kyiv hit by 110 missiles + 400 drones (20 Nov) \u00B7 Trump\u2013Xi\u2013Putin summit (19 Nov) \u00B7 ICJ: Myanmar committed genocide (19\u201320 Nov) \u00B7 'killer robot' talks end (21 Nov) \u00B7 Nvidia SEC-probe reports (19\u201320 Nov) \u00B7 Ramstein pledges (17 Nov) \u00B7 Iran strikes on Bahrain (17 Nov) \u00B7 Russian drones over Moldova (21 Nov).";

// ---------------------------------------------------------------- pictures
// Flat, original vector scenes drawn by this program — no photos, no
// borrowed artwork. Each scene is a few primitives on a tinted ground.
function ground(x: number, y: number, w: number, h: number, c: number[]) {
  rect(x, y, w, h, c);
  rect(x, y + h - 2, w, 2, RULE);
}
function flame(cx: number, cy: number, s: number) {
  poly([[cx - 9 * s, cy + 8 * s], [cx - 11 * s, cy - 2 * s], [cx - 4 * s, cy - 6 * s],
        [cx - 1 * s, cy - 12 * s], [cx + 3 * s, cy - 5 * s], [cx + 9 * s, cy - 3 * s],
        [cx + 10 * s, cy + 8 * s]], [232, 120, 40]);
  poly([[cx - 5 * s, cy + 8 * s], [cx - 6 * s, cy - 1 * s], [cx, cy - 6 * s],
        [cx + 5 * s, cy - 1 * s], [cx + 5 * s, cy + 8 * s]], [245, 190, 60]);
}
function drawArt(kind: string, x: number, y: number, w: number, h: number) {
  const cx = x + w / 2, cy = y + h / 2;
  switch (kind) {
    case "globe": { // COP31: a cracked globe over a broken pact
      ground(x, y, w, h, [214, 228, 222]);
      disc(cx, cy - 6, 34, [52, 110, 150]);
      poly([[cx - 30, cy - 18], [cx - 8, cy - 26], [cx + 6, cy - 10], [cx - 2, cy + 4], [cx - 26, cy - 2]], [46, 140, 90]);
      poly([[cx + 8, cy - 22], [cx + 30, cy - 14], [cx + 26, cy + 6], [cx + 12, cy + 2]], [46, 140, 90]);
      poly([[cx - 18, cy + 14], [cx + 4, cy + 10], [cx + 16, cy + 22], [cx - 8, cy + 26]], [46, 140, 90]);
      line(cx - 26, cy - 26, cx + 26, cy + 22, 4, RED);
      line(cx + 26, cy - 26, cx - 26, cy + 22, 4, RED);
      break;
    }
    case "chart": { // AI rout: red market slide
      ground(x, y, w, h, [240, 224, 212]);
      for (let i = 0; i < 5; i++) rect(x + 30 + i * 52, y + h - 34 - [18, 30, 12, 44, 8][i], 30, [18, 30, 12, 44, 8][i], i === 3 ? RED : NAVY);
      line(x + 22, y + 26, x + 90, y + 44, 4, RED);
      line(x + 90, y + 44, x + 150, y + 38, 4, RED);
      line(x + 150, y + 38, x + 220, y + 78, 4, RED);
      line(x + 220, y + 78, x + 292, y + 96, 4, RED);
      disc(x + 292, y + 96, 6, RED);
      break;
    }
    case "shield": { // Ukraine: shield under missile arcs
      ground(x, y, w, h, [222, 228, 238]);
      poly([[cx - 34, cy - 30], [cx + 34, cy - 30], [cx + 34, cy + 2], [cx, cy + 36], [cx - 34, cy + 2]], NAVY);
      poly([[cx - 24, cy - 20], [cx + 24, cy - 20], [cx + 24, cy + 2], [cx, cy + 24], [cx - 24, cy + 2]], [245, 205, 60]);
      line(x + 20, y + 14, cx - 20, cy - 26, 3, RED);
      line(x + 60, y + 8, cx - 4, cy - 30, 3, RED);
      line(x + 300, y + 12, cx + 22, cy - 24, 3, RED);
      disc(cx - 20, cy - 26, 4, RED); disc(cx - 4, cy - 30, 4, RED); disc(cx + 22, cy - 24, 4, RED);
      break;
    }
    case "factory": {
      ground(x, y, w, h, [238, 226, 214]);
      rect(x + 26, y + 44, 120, 58, [90, 88, 84]);
      poly([[x + 26, y + 44], [x + 56, y + 24], [x + 86, y + 44]], [70, 68, 64]);
      rect(x + 150, y + 30, 16, 72, [90, 88, 84]);
      rect(x + 176, y + 52, 100, 50, [110, 108, 102]);
      rect(x + 44, y + 62, 18, 18, [245, 205, 60]); rect(x + 74, y + 62, 18, 18, [245, 205, 60]);
      rect(x + 104, y + 62, 18, 18, [245, 205, 60]);
      flame(x + 158, y + 30, 1.1); flame(x + 200, y + 52, 0.9); flame(x + 240, y + 52, 1.2);
      disc(x + 158, y + 12, 14, [120, 120, 116], 0.7); disc(x + 190, y + 4, 18, [120, 120, 116], 0.6);
      break;
    }
    case "exam": {
      ground(x, y, w, h, [236, 232, 220]);
      poly([[x + 60, y + 20], [x + 130, y + 20], [x + 130, y + 96], [x + 60, y + 96]], WHITE);
      hline(x + 70, y + 34, 50, 3, INK); hline(x + 70, y + 46, 50, 3, GRAY);
      hline(x + 70, y + 58, 50, 3, GRAY); hline(x + 70, y + 70, 36, 3, GRAY);
      rect(x + 168, y + 30, 74, 52, RED);
      drawText("sans_bold", "OUT", x + 205, y + 56, 20, WHITE, "c");
      line(x + 150, y + 18, x + 178, y + 46, 4, INK);
      break;
    }
    case "flags": {
      ground(x, y, w, h, [224, 232, 228]);
      rect(x + 40, y + 24, 96, 60, [220, 20, 60]);
      poly([[x + 40, y + 24], [x + 88, y + 54], [x + 40, y + 84]], NAVY);
      rect(x + 176, y + 24, 96, 60, [255, 153, 51]);
      rect(x + 176, y + 44, 96, 20, WHITE);
      rect(x + 176, y + 64, 96, 20, [19, 136, 8]);
      disc(cx, cy + 8, 16, NAVY); disc(cx, cy + 8, 11, WHITE); disc(cx, cy + 8, 6, NAVY);
      break;
    }
    case "ball": {
      ground(x, y, w, h, [222, 232, 222]);
      rect(x + 24, y + 26, 120, 54, [30, 90, 40]);
      drawText("sans_bold", "4 - 0", x + 84, y + 62, 30, WHITE, "c");
      disc(cx + 66, cy + 18, 24, WHITE);
      poly([[cx + 66, cy - 2], [cx + 78, cy + 10], [cx + 74, cy + 28], [cx + 58, cy + 28], [cx + 54, cy + 10]], INK);
      break;
    }
    case "f1": {
      ground(x, y, w, h, [228, 228, 236]);
      for (let i = 0; i < 4; i++) for (let j = 0; j < 2; j++)
        rect(x + 30 + i * 16, y + 22 + j * 16, 16, 16, (i + j) % 2 ? INK : WHITE);
      poly([[x + 120, y + 78], [x + 210, y + 78], [x + 240, y + 58], [x + 200, y + 52], [x + 140, y + 56]], RED);
      disc(x + 150, y + 84, 12, INK); disc(x + 220, y + 84, 12, INK);
      disc(x + 150, y + 84, 5, [200, 200, 200]); disc(x + 220, y + 84, 5, [200, 200, 200]);
      line(x + 240, y + 58, x + 268, y + 40, 4, INK);
      break;
    }
    case "cricket": {
      ground(x, y, w, h, [232, 238, 220]);
      line(x + 60, y + 84, x + 120, y + 30, 8, [190, 150, 100]);
      rect(x + 118, y + 18, 14, 26, [190, 150, 100]);
      disc(cx + 62, cy - 12, 12, RED);
      drawText("serif_bold", "720/9", x + 200, y + 78, 26, NAVY, "c");
      break;
    }
    case "radar": {
      ground(x, y, w, h, [222, 230, 222]);
      disc(cx, cy, 40, [40, 90, 60]);
      ring(cx, cy, 40, 2, [120, 200, 140]); ring(cx, cy, 26, 2, [120, 200, 140]); ring(cx, cy, 12, 2, [120, 200, 140]);
      line(cx, cy, cx + 30, cy - 26, 3, [140, 230, 160]);
      disc(cx + 30, cy - 26, 4, [140, 230, 160]);
      disc(cx - 18, cy + 10, 5, RED); disc(cx + 14, cy + 16, 5, RED);
      break;
    }
    case "gavel": {
      ground(x, y, w, h, [236, 230, 220]);
      line(x + 70, y + 78, x + 240, y + 30, 10, [150, 110, 70]);
      rect(x + 210, y + 16, 60, 22, [120, 85, 50]);
      rect(x + 96, y + 78, 90, 12, [120, 85, 50]);
      disc(cx - 40, cy + 26, 6, RED); disc(cx + 30, cy + 26, 6, RED);
      break;
    }
    case "march": {
      ground(x, y, w, h, [238, 230, 222]);
      for (let i = 0; i < 5; i++) {
        const bx = x + 34 + i * 48;
        disc(bx + 12, y + 34, 10, [60, 60, 66]);
        poly([[bx, y + 92], [bx + 24, y + 46], [bx + 48, y + 92]], [i % 2 ? NAVY : RED]);
      }
      rect(x + 130, y + 14, 60, 26, WHITE);
      hline(x + 136, y + 22, 48, 3, RED); hline(x + 136, y + 30, 48, 3, INK);
      break;
    }
    case "virus": {
      ground(x, y, w, h, [236, 224, 228]);
      disc(cx - 20, cy - 6, 26, [140, 40, 60]);
      disc(cx + 26, cy + 14, 18, [140, 40, 60]);
      for (let k = 0; k < 8; k++) {
        const a = (k / 8) * Math.PI * 2;
        line(cx - 20 + Math.cos(a) * 26, cy - 6 + Math.sin(a) * 26, cx - 20 + Math.cos(a) * 36, cy - 6 + Math.sin(a) * 36, 3, [140, 40, 60]);
      }
      disc(cx - 28, cy - 12, 5, [220, 120, 140]); disc(cx - 12, cy + 2, 4, [220, 120, 140]);
      break;
    }
  }
}

// Small-cell scenes, designed for a 184x44 box: one tinted ground, one
// bold motif, nothing that can spill into the text below.
function drawMini(kind: string, x: number, y: number, w: number, h: number) {
  const cx = x + w / 2, cy = y + h / 2;
  switch (kind) {
    case "factory":
      ground(x, y, w, h, [238, 226, 214]);
      rect(x + 18, y + 16, 80, 22, [90, 88, 84]);
      rect(x + 104, y + 10, 10, 28, [90, 88, 84]);
      rect(x + 120, y + 22, 48, 16, [110, 108, 102]);
      flame(x + 109, y + 10, 0.7); flame(x + 140, y + 22, 0.6);
      break;
    case "exam":
      ground(x, y, w, h, [236, 232, 220]);
      rect(x + 60, y + 6, 44, 32, WHITE);
      hline(x + 66, y + 14, 32, 2, INK); hline(x + 66, y + 21, 32, 2, GRAY); hline(x + 66, y + 28, 24, 2, GRAY);
      rect(x + 116, y + 10, 34, 24, RED);
      drawText("sans_bold", "OUT", x + 133, y + 27, 11, WHITE, "c");
      break;
    case "flags":
      ground(x, y, w, h, [224, 232, 228]);
      rect(x + 44, y + 8, 44, 28, [220, 20, 60]);
      poly([[x + 44, y + 8], [x + 66, y + 22], [x + 44, y + 36]], NAVY);
      rect(x + 96, y + 8, 44, 28, [255, 153, 51]);
      rect(x + 96, y + 17, 44, 9, WHITE);
      rect(x + 96, y + 26, 44, 10, [19, 136, 8]);
      break;
    case "ball":
      ground(x, y, w, h, [222, 232, 222]);
      rect(x + 16, y + 8, 84, 28, [30, 90, 40]);
      drawText("sans_bold", "4 - 0", x + 58, y + 29, 18, WHITE, "c");
      disc(cx + 52, cy, 15, WHITE);
      poly([[cx + 52, cy - 10], [cx + 60, cy - 1], [cx + 57, cy + 10], [cx + 47, cy + 10], [cx + 44, cy - 1]], INK);
      break;
    case "f1":
      ground(x, y, w, h, [228, 228, 236]);
      for (let i = 0; i < 4; i++) for (let j = 0; j < 2; j++)
        rect(x + 16 + i * 11, y + 8 + j * 11, 11, 11, (i + j) % 2 ? INK : WHITE);
      poly([[x + 84, y + 34], [x + 140, y + 34], [x + 160, y + 22], [x + 128, y + 18], [x + 96, y + 22]], RED);
      disc(x + 104, y + 36, 7, INK); disc(x + 146, y + 36, 7, INK);
      break;
    case "cricket":
      ground(x, y, w, h, [232, 238, 220]);
      line(x + 30, y + 36, x + 62, y + 10, 6, [190, 150, 100]);
      disc(cx + 30, cy - 6, 8, RED);
      drawText("serif_bold", "720/9", x + 140, y + 30, 17, NAVY, "c");
      break;
    case "radar":
      ground(x, y, w, h, [222, 230, 222]);
      disc(cx, cy, 19, [40, 90, 60]);
      ring(cx, cy, 19, 1.5, [120, 200, 140]); ring(cx, cy, 10, 1.5, [120, 200, 140]);
      line(cx, cy, cx + 14, cy - 12, 2, [140, 230, 160]);
      disc(cx - 8, cy + 5, 3, RED);
      break;
    case "gavel":
      ground(x, y, w, h, [236, 230, 220]);
      line(x + 50, y + 34, x + 150, y + 12, 7, [150, 110, 70]);
      rect(x + 132, y + 4, 34, 13, [120, 85, 50]);
      rect(x + 66, y + 34, 52, 7, [120, 85, 50]);
      break;
    case "march":
      ground(x, y, w, h, [238, 230, 222]);
      for (let i = 0; i < 4; i++) {
        const bx = x + 30 + i * 38;
        disc(bx + 10, y + 14, 7, [60, 60, 66]);
        poly([[bx, y + 40], [bx + 20, y + 20], [bx + 40, y + 40]], [i % 2 ? NAVY : RED]);
      }
      rect(x + 118, y + 6, 40, 14, WHITE);
      hline(x + 122, y + 11, 32, 2, RED);
      break;
    case "virus":
      ground(x, y, w, h, [236, 224, 228]);
      disc(cx - 14, cy - 2, 15, [140, 40, 60]);
      disc(cx + 18, cy + 8, 10, [140, 40, 60]);
      for (let k = 0; k < 6; k++) {
        const a = (k / 6) * Math.PI * 2;
        line(cx - 14 + Math.cos(a) * 15, cy - 2 + Math.sin(a) * 15, cx - 14 + Math.cos(a) * 21, cy - 2 + Math.sin(a) * 21, 2, [140, 40, 60]);
      }
      break;
  }
}

// ---------------------------------------------------------------- world map
// Rough equirectangular continents (lon/lat), drawn small and stylised.
const CONTINENTS: [number, number][][] = [
  [[-168, 66], [-140, 70], [-120, 72], [-95, 80], [-80, 73], [-60, 60], [-55, 47], [-70, 42], [-75, 35], [-80, 26], [-85, 20], [-92, 15], [-97, 16], [-105, 20], [-115, 28], [-125, 40], [-125, 49], [-140, 60], [-155, 58], [-165, 60]],
  [[-80, 10], [-75, 5], [-60, 0], [-50, -5], [-35, -8], [-40, -20], [-48, -28], [-58, -35], [-65, -45], [-70, -52], [-73, -40], [-72, -20], [-78, -5]],
  [[30, 70], [45, 68], [60, 69], [70, 72], [90, 75], [110, 76], [130, 72], [160, 70], [178, 66], [170, 60], [162, 56], [158, 50], [142, 45], [140, 40], [130, 35], [127, 35], [122, 30], [120, 25], [110, 20], [105, 10], [100, 8], [95, 15], [90, 22], [85, 20], [80, 13], [75, 8], [72, 20], [65, 25], [58, 26], [55, 26], [50, 29], [48, 30], [44, 29], [40, 32], [36, 36], [30, 36], [28, 40], [25, 40], [30, 45], [30, 50], [28, 55], [30, 60]],
  [[-10, 36], [-9, 43], [-2, 48], [0, 51], [5, 53], [8, 57], [10, 59], [18, 56], [21, 55], [24, 58], [28, 60], [30, 62], [32, 70], [40, 68], [44, 66], [40, 60], [35, 55], [30, 50], [28, 45], [23, 40], [19, 42], [12, 44], [3, 43], [-2, 37]],
  [[-6, 35], [10, 37], [20, 32], [32, 31], [35, 28], [43, 12], [51, 11], [48, 0], [40, -10], [36, -18], [32, -26], [26, -34], [18, -35], [12, -18], [9, -1], [9, 4], [-8, 5], [-13, 8], [-17, 15], [-16, 25], [-10, 31]],
  [[113, -22], [114, -30], [115, -35], [120, -34], [124, -33], [129, -32], [132, -32], [135, -35], [137, -35], [140, -38], [145, -38], [150, -37], [153, -32], [153, -27], [150, -22], [146, -19], [142, -15], [142, -11], [137, -12], [135, -15], [132, -12], [130, -13], [126, -14], [122, -17], [118, -20]],
  [[167, -45], [174, -41], [178, -38], [175, -36], [172, -40]],
  [[-45, 60], [-40, 64], [-30, 68], [-22, 70], [-25, 76], [-35, 80], [-50, 80], [-58, 76], [-55, 70], [-52, 64]],
];
const PINS: [number, number, number][] = [
  [1, 30.7, 36.9], [2, -74, 40.7], [3, 30.5, 50.5], [4, 106.3, -6.3],
  [5, 127, 37.5], [6, 77.2, 28.6], [7, -2.99, 53.4], [8, -115.1, 36.2],
  [9, 174.8, -41.3], [10, 50.6, 26.2], [11, 96.2, 19.8], [12, -9.1, 38.7],
  [13, 23, -2],
];
function drawMap(x: number, y: number, w: number, h: number) {
  rect(x, y, w, h, [214, 228, 232]);
  const lon2x = (lon: number) => x + ((lon + 170) / 360) * w;
  const lat2y = (lat: number) => y + ((78 - lat) / 136) * h;
  for (const cont of CONTINENTS) {
    poly(cont.map(([lo, la]) => [lon2x(lo), lat2y(la)] as [number, number]), [196, 196, 178]);
  }
  for (const [n, lo, la] of PINS) {
    const px2 = lon2x(lo), py2 = lat2y(la);
    disc(px2, py2, 8, RED);
    ring(px2, py2, 8, 1.5, WHITE);
    drawText("sans_bold", String(n), px2, py2 + 3.5, 10, WHITE, "c");
  }
}

// ---------------------------------------------------------------- layout
const MX = 26;                 // left margin
const CW = 972;                // content width
const CX = MX + CW;            // right edge

// Kicker bar
rect(0, 0, W, 30, BLACK);
drawText("sans_bold", "THE WORLD IN ONE DAY", MX, 21, 15, WHITE);
drawText("sans_bold", "35 STORIES \u00B7 7 REGIONS \u00B7 ALL DATED MONDAY 23 NOVEMBER 2026", CX, 20, 12, WHITE, "r");

// Masthead
drawText("serif_bold", "Monday 23 November 2026", W / 2, 88, 54, INK, "c");
hline(MX, 102, CW, 2, INK);
hline(MX, 106, CW, 1, INK);

// Sub-headline
drawText("serif_italic", "COP31 ends with no deal \u00B7 Nasdaq's worst week since March 2020 \u00B7 Kyiv pleads for Patriots",
  W / 2, 128, 17, INK, "c");

// Stat strip: 6 big numbers with labels
{
  const bw = CW / 6;
  for (let i = 0; i < 6; i++) {
    const bx = MX + i * bw;
    hline(bx + 4, 140, bw - 8, 2, RED);
    drawText("serif_bold", STATS[i][0], bx + bw / 2, 170, 26, i === 0 ? RED : NAVY, "c");
    const lab = wrap("sans_bold", STATS[i][1], 9, bw - 12);
    for (let j = 0; j < lab.length; j++)
      drawText("sans_bold", lab[j], bx + bw / 2, 186 + j * 11, 9, GRAY, "c");
  }
}

// Region caption + bar (counts are the real counts from this page's 35 stories)
drawText("sans_bold", "STORIES BY REGION", MX, 208, 10, INK);
{
  const parts = REGIONS.map(([n, c]) => `${n} ${c}`).join("  \u00B7  ");
  drawText("sans_bold", parts, CX, 208, 10, GRAY, "r");
}
{
  let bx = MX;
  for (const [name, count, col] of REGIONS) {
    const segW = Math.round((count / 35) * CW);
    rect(bx, 214, segW, 16, col);
    drawText("sans_bold", String(count), bx + segW / 2, 226, 10, WHITE, "c");
    bx += segW;
  }
}

// 3 lead stories
{
  const colW = 316, gap = 12, y0 = 240;
  for (let i = 0; i < 3; i++) {
    const lx = MX + i * (colW + gap);
    const L = LEADS[i];
    drawArt(L.art, lx, y0, colW, 120);
    rect(lx, y0 + 124, colW, 18, RED);
    drawText("sans_bold", `${L.n} \u00B7 ${L.tag}`, lx + 8, y0 + 137, 11, WHITE);
    const headLines = wrap("serif_bold", L.head, 19, colW);
    for (let j = 0; j < headLines.length; j++)
      drawText("serif_bold", headLines[j], lx, y0 + 164 + j * 22, 19, INK);
    const bodyTop = y0 + 164 + headLines.length * 22 + 6;
    const nBody = drawPara("serif", L.body, lx, bodyTop, 12, colW, INK, 15);
    drawText("sans_bold", L.src.toUpperCase(), lx, bodyTop + nBody * 15 + 12, 9, GRAY);
  }
}
hline(MX, 530, CW, 1, RULE);

// 10 small stories: 5 columns x 2 rows
{
  const colW = 184, gap = 13, rowH = 126, y0 = 538;
  for (let i = 0; i < 10; i++) {
    const col = i % 5, row = Math.floor(i / 5);
    const sx = MX + col * (colW + gap);
    const sy = y0 + row * rowH;
    const S = SMALL[i];
    drawMini(S.art, sx, sy, colW, 44);
    drawText("sans_bold", `${S.n} \u00B7 ${S.tag}`, sx, sy + 58, 9, RED);
    drawText("sans_bold", SHORT_SRC[S.n], sx + colW, sy + 58, 8, GRAY, "r");
    const headLines = wrap("serif_bold", S.head, 12, colW);
    for (let j = 0; j < Math.min(2, headLines.length); j++)
      drawText("serif_bold", headLines[j], sx, sy + 74 + j * 14, 12, INK);
    drawPara("serif", S.body, sx, sy + 100, 10, colW, INK, 11.5);
  }
}
hline(MX, 796, CW, 1, RULE);

// Bottom: world map (left) + ALSO list (right)
{
  const by = 804;
  drawText("sans_bold", "WHERE IT HAPPENED", MX, by + 12, 11, INK);
  drawMap(MX, by + 20, 304, 120);
  const ax = MX + 320;
  drawText("sans_bold", "ALSO ON MONDAY 23 NOVEMBER \u2014 22 MORE STORIES", ax, by + 12, 11, INK);
  const colW = 320, lh = 11.5;
  for (let i = 0; i < 22; i++) {
    const col = Math.floor(i / 11), row = i % 11;
    const lx = ax + col * (colW + 12);
    const ly = by + 18 + row * lh;
    const [n, text, src] = ALSO[i];
    drawText("sans_bold", String(n), lx, ly + 9, 10, RED);
    let size = 9.5;
    let line = `${text} \u2014 ${src}`;
    while (size > 8 && textWidth("serif", line, size) > colW - 24) size -= 0.5;
    while (textWidth("serif", line, size) > colW - 24 && line.length > 12)
      line = line.slice(0, -4) + "\u2026";
    drawText("serif", line, lx + 22, ly + 9, size, INK);
  }
}

// DATE CHECK — what was deliberately left out
{
  const dy = 950;
  rect(MX, dy, CW, 48, PAPER);
  for (let t = 0; t < 2; t++) { hline(MX, dy + t, CW, 1, RED); hline(MX, dy + 46 + t, CW, 1, RED); }
  vline(MX, dy, 48, 2, RED); vline(CX - 2, dy, 48, 2, RED);
  drawText("sans_bold", "DATE CHECK \u2014 WHAT WE DELIBERATELY LEFT OUT", MX + 8, dy + 13, 10, RED);
  drawPara("serif", DATE_CHECK, MX + 8, dy + 27, 9.5, CW - 16, INK, 11.5);
}

// Footer
drawText("serif", "Every story happened, or was first reported, on Monday 23 November 2026 \u00B7 Sources named beside each story \u00B7 All illustrations drawn for this page",
  W / 2, 1014, 9, GRAY, "c");

// ---------------------------------------------------------------- run
const outDir = process.env.MAKEFUN_OUTPUT_DIR || "/output";
const bytes = writePNG(`${outDir}/entry.png`);
console.log(JSON.stringify({ file: `${outDir}/entry.png`, bytes, size: "1024x1024" }));
