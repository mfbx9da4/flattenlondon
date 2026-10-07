/* Flatten London: the routing worker.
 *
 * Adapted from flattensf (MIT) by Drew Edwards,
 * https://github.com/almostimplemented/flattensf : engine.js (decode,
 * MinHeap, Dijkstra, reverse bounds, BOA*, summaries, geometry) and simple.js
 * (the provisional family, finishFamily, thinFrontier, resample, runs).
 * Copyright (c) Drew Edwards, released under the MIT licence; the London
 * changes are MIT too.
 *
 * One classic worker script, no imports, no build step. It owns the street
 * graph, which arrives in 4 km tiles (docs/design.md section 4): it loads the
 * tile index, fetches tiles on demand, snaps points to junctions and finds the
 * shortest route, the flattest route (length + 200 x climbing) and every route
 * on the distance-versus-climbing frontier between them. The page talks to it
 * with the messages of design.md section 5.1; extensions are documented in
 * docs/payload.md under "worker".
 *
 * What changed from SF, and why:
 *  - tiles with global ids: every id in a tile is global, so the worker keeps
 *    graph-sized typed arrays and copies each tile into its id ranges when it
 *    arrives. A node's mode flag doubles as "its tile is loaded", so arcs into
 *    tiles that are not loaded are skipped by the same test that keeps a
 *    route inside the mode's strongly connected component;
 *  - A* instead of Dijkstra for the shortest and flattest routes (the cost is
 *    SF's length + alpha * climbing in integer 5 cm units), when the tiles
 *    pass a check that node points sit where their edges end;
 *  - BOA* bounds are reverse Dijkstras over the loaded tiles only, cut at the
 *    length cap and at the cap ellipse, instead of over the whole graph;
 *  - BOA* starts with SF's tolerances and raises them only when the label
 *    count is heading past a budget (long cross-London trips), then stops at
 *    a hard label cap or time limit and says so (truncated);
 *  - every search runs in time slices so a cancel or a newer request is
 *    honoured within a slice, and the frontier is thinned on (length,
 *    climbing) before any geometry is built;
 *  - unknown modes are refused (SF routed them as a fewest-arcs walk).
 */
"use strict";

/* -------------------------------------------------------------- constants */
// SF parity (simple.js:35-41); index.json meta overrides them when present
let ALPHA_MAX = 200;        // flattest end: a metre of climb costs 200 m of walking
let EPS_GAIN_CM = 50;       // frontier points within 50 cm of climbing are merged
let EPS_NODE_CM = 10;       // the same tolerance at intermediate nodes
let MAX_ROUTES = 30;        // most routes on the slider
const PROFILE_SAMPLES = 160;
const RUN_MIN_M = 60;       // turn list; route labels use the runs of 80 m or more
const GRADE_MIN_M = 15;     // "steepest" is held over at least this far (config reliable_grade_length_m)
const HEAP_KEY_BASE = 1 << 20;   // BOA* key: f1 * 2^20 + min(f2, 2^20 - 1)
const INF = 0x3fffffff;          // "no bound" in the Int32 bound arrays

// A* bound: straight-line distance shrunk so it stays below every path length
// despite 5 cm rounding of lengths, micro-degree coordinates, BNG scale
// (0.9998 in London) and one cos(lat) for the whole search
const H_FACTOR = 0.99;
const H_MARGIN_M = 1;
// ... which holds only when node coordinates are where the edge geometry
// ends (design.md 3.1). Tiles are checked as they load: if any arc is shorter
// than H_FACTOR x its chord by more than this (quantisation noise is about
// 0.2 m), the straight-line bounds are switched off and searches are plain
// Dijkstra (SF's own graph fails it by up to 101 m: first-writer node points)
const H_EXCESS_MAX_M = 0.5;

// tunables; init may override them ({tuning: {...}}, for tests)
const TUNING_DEFAULTS = {
  slice_ms: 25,             // longest uninterrupted run of work
  frontier_ms: 10000,       // BOA* time budget; then the short end found so far is kept
  max_labels: 4e6,          // BOA* label cap (SF parity): 16 B a label plus the heap, about 110 MB
  label_target: 2e6,        // raise the tolerances when the search is heading past this many labels
  eps_frac: 60,             // ... but never merge routes closer than (climb range) / eps_frac
  adapt_every: 1 << 16,     // BOA* labels between looks at the projected label count
  snap_max_m: 2000,         // farther than this from any junction: no node
  snap_prefetch_m: 300,     // tiles this close to a snapped point are fetched together
  fetch_concurrency: 6,
  grow_rounds: 3,           // corridor growth rounds (design.md section 5)
  bridge_routes: 3,         // weighted routes that span a truncated frontier's gap
  progress_ms: 100,         // progress messages at most this often
};

const TYPES = {
  i1: Int8Array, u1: Uint8Array, i2: Int16Array, u2: Uint16Array,
  i4: Int32Array, u4: Uint32Array, f4: Float32Array, f8: Float64Array,
};
const UTF8 = new TextDecoder();
const now = () => performance.now();

/* ----------------------------------------------------------------- decode */
/* GitHub Pages serves .gz as application/gzip without Content-Encoding, so
 * the bytes arrive compressed; a host that does set Content-Encoding hands us
 * plain bytes. The gzip magic number tells the two apart (SF engine.js). */
async function inflateBytes(bytes) {
  if (!(bytes.length > 2 && bytes[0] === 0x1f && bytes[1] === 0x8b)) return bytes;
  if (typeof DecompressionStream === "undefined") {
    throw new Error("this browser has no DecompressionStream; please use a "
      + "current version of Chrome, Firefox, Edge or Safari");
  }
  const stream = new Blob([bytes]).stream().pipeThrough(new DecompressionStream("gzip"));
  return new Uint8Array(await new Response(stream).arrayBuffer());
}

/* An FLT1 tile: "FLT1", uint32 LE header length H, H bytes of JSON
 * {arrays: {name: {t, o, n}}, strings: {name: {o, b}}}, offsets from the start
 * of the file, every array on an 8-byte boundary. Arrays become zero-copy
 * views (copied only if a producer ever misaligns one). */
function parseFLT1(raw) {
  if (raw.length < 8 || raw[0] !== 0x46 || raw[1] !== 0x4c || raw[2] !== 0x54 || raw[3] !== 0x31) {
    throw new Error("not an FLT1 tile");
  }
  const H = (raw[4] | (raw[5] << 8) | (raw[6] << 16) | (raw[7] << 24)) >>> 0;
  if (8 + H > raw.length) throw new Error("truncated FLT1 header");
  const header = JSON.parse(UTF8.decode(raw.subarray(8, 8 + H)));
  const arrays = {}, strings = {};
  for (const name of Object.keys(header.arrays || {})) {
    const m = header.arrays[name], T = TYPES[m.t];
    if (!T) throw new Error("unknown dtype " + m.t + " for " + name);
    const len = m.n * T.BYTES_PER_ELEMENT;
    if (m.o < 8 + H || m.o + len > raw.length) throw new Error("array " + name + " out of bounds");
    const start = raw.byteOffset + m.o;
    arrays[name] = start % T.BYTES_PER_ELEMENT === 0
      ? new T(raw.buffer, start, m.n)
      : new T(raw.slice(m.o, m.o + len).buffer, 0, m.n);
  }
  for (const name of Object.keys(header.strings || {})) {
    const s = header.strings[name];
    if (s.o + s.b > raw.length) throw new Error("string " + name + " out of bounds");
    strings[name] = raw.subarray(s.o, s.o + s.b);
  }
  return { header, arrays, strings };
}

/* Google encoded polyline (precision 5, lat then lon, delta coding restarted
 * per edge), read straight from the ASCII bytes; appends lat, lon pairs. */
function decodePolyline(bytes, start, end, out) {
  let i = start, lat = 0, lon = 0;
  while (i < end) {
    let b, shift = 0, result = 0;
    do { b = bytes[i++] - 63; result |= (b & 0x1f) << shift; shift += 5; } while (b >= 0x20);
    lat += (result & 1) ? ~(result >> 1) : (result >> 1);
    shift = 0; result = 0;
    do { b = bytes[i++] - 63; result |= (b & 0x1f) << shift; shift += 5; } while (b >= 0x20);
    lon += (result & 1) ? ~(result >> 1) : (result >> 1);
    out.push(lat / 1e5, lon / 1e5);
  }
  return out;
}

class HttpError extends Error {
  constructor(url, status) { super("could not load " + url + " (" + status + ")"); this.status = status; }
}

/* ------------------------------------------------------------------- heap */
/* A binary min-heap of (float key, int value) pairs on typed arrays, exactly
 * SF's (ties stop sifting; pop leaves the key in topKey). */
class MinHeap {
  constructor(cap = 1 << 16) { this.k = new Float64Array(cap); this.v = new Int32Array(cap); this.n = 0; this.topKey = 0; }
  reset() { this.n = 0; }
  shrink(cap) { if (this.k.length > cap) { this.k = new Float64Array(cap); this.v = new Int32Array(cap); } this.n = 0; }
  push(key, val) {
    if (this.n === this.k.length) {
      const nk = new Float64Array(this.k.length * 2), nv = new Int32Array(this.v.length * 2);
      nk.set(this.k); nv.set(this.v); this.k = nk; this.v = nv;
    }
    const k = this.k, v = this.v;
    let i = this.n++;
    k[i] = key; v[i] = val;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (k[p] <= k[i]) break;
      const tk = k[p], tv = v[p]; k[p] = k[i]; v[p] = v[i]; k[i] = tk; v[i] = tv; i = p;
    }
  }
  pop() {
    const k = this.k, v = this.v;
    const top = v[0]; this.topKey = k[0];
    this.n--;
    if (this.n > 0) {
      k[0] = k[this.n]; v[0] = v[this.n];
      let i = 0;
      for (;;) {
        const l = 2 * i + 1, r = l + 1; let m = i;
        if (l < this.n && k[l] < k[m]) m = l;
        if (r < this.n && k[r] < k[m]) m = r;
        if (m === i) break;
        const tk = k[m], tv = v[m]; k[m] = k[i]; v[m] = v[i]; k[i] = tk; v[i] = tv; i = m;
      }
    }
    return top;
  }
}

/* -------------------------------------------------------------- geography */
/* Metres per degree of longitude and latitude on the WGS84 ellipsoid at one
 * latitude. Over Greater London one factor pair is good to 0.5 %. */
function metresPerDegree(latDeg) {
  const a = 6378137, e2 = 0.00669437999014;
  const p = latDeg * Math.PI / 180, s = Math.sin(p), w = 1 - e2 * s * s;
  const N = a / Math.sqrt(w), M = a * (1 - e2) / (w * Math.sqrt(w));
  return { kx: N * Math.cos(p) * Math.PI / 180, ky: M * Math.PI / 180 };
}

/* Smallest |p - s| + |p - t| over an axis-aligned rectangle [x0, y0, x1, y1]
 * (local metres): the distance s-t if the segment crosses the rectangle, else
 * the minimum over its four sides, each a convex function of position. */
function rectEllipseMin(r, sx, sy, tx, ty) {
  const D = Math.hypot(tx - sx, ty - sy);
  if (segmentHitsRect(r, sx, sy, tx, ty)) return D;
  const f = (x, y) => Math.hypot(x - sx, y - sy) + Math.hypot(x - tx, y - ty);
  const side = (ax, ay, bx, by) => {
    let lo = 0, hi = 1;
    for (let it = 0; it < 60; it++) {
      const m1 = lo + (hi - lo) / 3, m2 = hi - (hi - lo) / 3;
      if (f(ax + (bx - ax) * m1, ay + (by - ay) * m1) <= f(ax + (bx - ax) * m2, ay + (by - ay) * m2)) hi = m2;
      else lo = m1;
    }
    const m = (lo + hi) / 2;
    return f(ax + (bx - ax) * m, ay + (by - ay) * m);
  };
  return Math.min(side(r[0], r[1], r[2], r[1]), side(r[2], r[1], r[2], r[3]),
    side(r[2], r[3], r[0], r[3]), side(r[0], r[3], r[0], r[1]));
}

/* Liang-Barsky: does segment s-t meet the rectangle? */
function segmentHitsRect(r, sx, sy, tx, ty) {
  let t0 = 0, t1 = 1;
  const dx = tx - sx, dy = ty - sy;
  const clip = (p, q) => {
    if (p === 0) return q >= 0;
    const t = q / p;
    if (p < 0) { if (t > t1) return false; if (t > t0) t0 = t; return true; }
    if (t < t0) return false; if (t < t1) t1 = t; return true;
  };
  return clip(-dx, sx - r[0]) && clip(dx, r[2] - sx) && clip(-dy, sy - r[1]) && clip(dy, r[3] - sy);
}

/* ------------------------------------------------------- the tiled graph */
/* Graph-sized typed arrays, filled tile by tile. Arrays a tile has not filled
 * stay zero, and node_flags == 0 marks a node as unusable in both modes, so an
 * arc whose head tile is not loaded fails the same test as an arc leaving the
 * mode's strongly connected component. */
class TiledGraph {
  constructor(index, base, fetchFn) {
    const meta = index.meta;
    this.meta = meta;
    this.base = base;
    this.fetch = fetchFn;
    const sc = meta.scales || {};
    this.DM = sc.dm || 20; this.CM = sc.cm || 100; this.GRADE = sc.grade || 10000; this.COORD = sc.coord || 1e6;
    const n = this.n = meta.n_nodes, m = this.m = meta.n_arcs, ne = this.ne = meta.n_edges;
    this.tiles = (index.tiles || []).map((t, k) => ({
      i: t.i, j: t.j, node0: t.node0, nodes: t.nodes, arc0: t.arc0, arcs: t.arcs,
      edge0: t.edge0, edges: t.edges, bbox: t.bbox, url: t.url, bytes: t.bytes || 0, k,
      loaded: false, promise: null, geom: null, geomOff: null,
    }));
    const lookup = (key, count) => {
      const list = this.tiles.filter((t) => t[count] > 0).sort((a, b) => a[key] - b[key]);
      return { list, start: Int32Array.from(list.map((t) => t[key])) };
    };
    this.byNode = lookup("node0", "nodes");
    this.byArc = lookup("arc0", "arcs");
    this.byEdge = lookup("edge0", "edges");

    this.lon = new Int32Array(n); this.lat = new Int32Array(n);
    this.elev = new Int16Array(n); this.nflags = new Uint8Array(n);
    this.indptr = new Int32Array(n + 1);
    this.head = new Int32Array(m); this.aedge = new Int32Array(m); this.atail = new Int32Array(m);
    this.alen = new Uint16Array(m); this.again = new Uint16Array(m); this.aloss = new Uint16Array(m);
    this.amaxg = new Int16Array(m); this.aflags = new Uint8Array(m);
    this.ename = new Int32Array(ne);
    this.version = 0;            // bumps whenever a tile lands
    this.hExcess = 0;            // worst H_FACTOR x chord - length over loaded arcs (m)
    this.loaded = [];            // loaded tiles
    this.names = [];
    this.namesPromise = Promise.resolve();
  }

  static find(lk, id, count) {
    const s = lk.start;
    let lo = 0, hi = s.length - 1, best = -1;
    while (lo <= hi) {
      const mid = (lo + hi) >> 1;
      if (s[mid] <= id) { best = mid; lo = mid + 1; } else hi = mid - 1;
    }
    if (best < 0) return null;
    const t = lk.list[best];
    return id < s[best] + t[count] ? t : null;
  }
  tileOfNode(v) { return TiledGraph.find(this.byNode, v, "nodes"); }
  tileOfArc(a) { return TiledGraph.find(this.byArc, a, "arcs"); }
  tileOfEdge(e) { return TiledGraph.find(this.byEdge, e, "edges"); }
  url(rel) { return new URL(rel, this.base).href; }

  loadNames(spec) {
    if (!spec || !spec.url) return this.namesPromise;
    this.namesPromise = (async () => {
      const res = await this.fetch(this.url(spec.url));
      if (!res.ok) throw new HttpError(spec.url, res.status);
      const raw = await inflateBytes(new Uint8Array(await res.arrayBuffer()));
      this.names = JSON.parse(UTF8.decode(raw));
    })();
    return this.namesPromise;
  }

  /* fetch, inflate, parse and install one tile; concurrent callers share it */
  loadTile(t) {
    if (t.loaded) return Promise.resolve(t);
    if (t.promise) return t.promise;
    t.promise = (async () => {
      const url = this.url(t.url);
      const res = await this.fetch(url);
      if (!res.ok) throw new HttpError(url, res.status);
      const raw = await inflateBytes(new Uint8Array(await res.arrayBuffer()));
      if (!t.loaded) this.install(t, parseFLT1(raw));
      return t;
    })();
    t.promise.catch(() => { t.promise = null; });   // a later request may retry
    return t.promise;
  }

  /* load tiles with a small pool of parallel fetches; stops issuing new
   * fetches once keepGoing() says the work is stale */
  async loadTiles(list, conc, onTile, keepGoing) {
    let next = 0;
    const run = async () => {
      while (next < list.length) {
        if (keepGoing && !keepGoing()) return;
        const t = list[next++];
        await this.loadTile(t);
        if (onTile) onTile(t);
      }
    };
    const pool = [];
    for (let k = 0; k < Math.min(conc, list.length); k++) pool.push(run());
    await Promise.all(pool);
  }

  install(t, tile) {
    const A = tile.arrays, where = "tile " + t.i + "_" + t.j + ": ";
    const need = (name, count) => {
      const x = A[name];
      if (!x) throw new Error(where + "missing array " + name);
      if (count >= 0 && x.length !== count) throw new Error(where + name + " has " + x.length + " entries, expected " + count);
      return x;
    };
    const nn = t.nodes, na = t.arcs, ne = t.edges, n0 = t.node0, a0 = t.arc0, e0 = t.edge0;
    if (n0 + nn > this.n || a0 + na > this.m || e0 + ne > this.ne) throw new Error(where + "id range outside the graph");
    const lip = need("indptr", nn + 1);
    if (lip[0] !== 0 || lip[nn] !== na) throw new Error(where + "indptr does not span the tile's arcs");
    const head = need("arc_head", na), aedge = need("arc_edge", na);
    for (let k = 0; k < na; k++) {
      if (head[k] < 0 || head[k] >= this.n || aedge[k] < 0 || aedge[k] >= this.ne) throw new Error(where + "arc id out of range");
    }
    const flags = need("node_flags", nn);
    this.lon.set(need("node_lon", nn), n0);
    this.lat.set(need("node_lat", nn), n0);
    this.elev.set(need("node_elev", nn), n0);
    const gp = this.indptr, at = this.atail;
    for (let i = 0; i < nn; i++) {
      gp[n0 + i] = a0 + lip[i];
      for (let a = lip[i]; a < lip[i + 1]; a++) at[a0 + a] = n0 + i;
    }
    gp[n0 + nn] = a0 + na;
    this.head.set(head, a0);
    this.aedge.set(aedge, a0);
    this.alen.set(need("arc_len", na), a0);
    this.again.set(need("arc_gain", na), a0);
    this.aloss.set(need("arc_loss", na), a0);
    this.amaxg.set(need("arc_maxgrade", na), a0);
    this.aflags.set(need("arc_flags", na), a0);
    this.ename.set(need("edge_name", ne), e0);
    const off = need("geom_off", ne + 1);
    const geom = tile.strings.geom;
    if (!geom || off[ne] > geom.length) throw new Error(where + "geometry string missing or short");
    t.geomOff = off.slice();        // own copies, so the inflated buffer can go
    t.geom = geom.slice(0, off[ne]);
    this.checkChords(t, lip, head, need("arc_len", na));
    this.nflags.set(flags, n0);     // last: from here on the nodes count as loaded
    t.loaded = true;
    this.loaded.push(t);
    this.version++;
  }

  /* straight-line bounds need every arc at least as long as H_FACTOR x the
   * chord between its nodes; checked on the arcs whose head is already here */
  checkChords(t, lip, head, alen) {
    const k = metresPerDegree((t.bbox ? (t.bbox[1] + t.bbox[3]) / 2 : this.lat[t.node0] / this.COORD));
    const kx = H_FACTOR * k.kx / this.COORD, ky = H_FACTOR * k.ky / this.COORD, lon = this.lon, lat = this.lat;
    let worst = this.hExcess;
    for (let i = 0; i < t.nodes; i++) {
      const u = t.node0 + i;
      for (let a = lip[i]; a < lip[i + 1]; a++) {
        const v = head[a];
        if (!(v >= t.node0 && v < t.node0 + t.nodes) && this.nflags[v] === 0) continue;   // head not loaded yet
        const dx = (lon[v] - lon[u]) * kx, dy = (lat[v] - lat[u]) * ky;
        const ex = Math.sqrt(dx * dx + dy * dy) - alen[a] / this.DM;
        if (ex > worst) worst = ex;
      }
    }
    this.hExcess = worst;
  }
  get straightBounds() { return this.hExcess <= H_EXCESS_MAX_M; }

  nodeLon(v) { return this.lon[v] / this.COORD; }
  nodeLat(v) { return this.lat[v] / this.COORD; }

  /* metres between two nodes */
  nodeDist(u, v) {
    const k = metresPerDegree((this.lat[u] + this.lat[v]) / 2 / this.COORD);
    return Math.hypot((this.lon[u] - this.lon[v]) / this.COORD * k.kx, (this.lat[u] - this.lat[v]) / this.COORD * k.ky);
  }

  /* metres from a point to a tile's bbox (0 inside); bbox covers its nodes */
  static bboxDist(b, lon, lat, k) {
    const dx = Math.max(b[0] - lon, 0, lon - b[2]) * k.kx, dy = Math.max(b[1] - lat, 0, lat - b[3]) * k.ky;
    return Math.hypot(dx, dy);
  }

  /* Nearest node with the mode bit, in metres (cos-scaled longitude), exactly:
   * tiles are visited by distance to their bbox, loading each on the way, and
   * the search stops once the next bbox is farther than the best node.
   * (SF searched raw degrees, which overweights east-west offsets 1.6x here.) */
  async snap(lon, lat, bit, maxM, keepGoing, prefetchM = 300) {
    const k = metresPerDegree(lat);
    const cand = [];
    for (const t of this.tiles) {
      if (t.nodes > 0 && t.bbox) cand.push({ t, d: TiledGraph.bboxDist(t.bbox, lon, lat, k) });
    }
    cand.sort((a, b) => a.d - b.d || a.t.node0 - b.t.node0);
    if (!cand.length || cand[0].d > maxM) return { error: "outside" };
    // fetch the close ones together; most snaps need only these
    await Promise.all(cand.filter((c) => c.d <= prefetchM).map((c) => this.loadTile(c.t)));
    const plon = lon * this.COORD, plat = lat * this.COORD, kx = k.kx / this.COORD, ky = k.ky / this.COORD;
    let best = -1, bestD = Infinity;
    for (const c of cand) {
      if (c.d > Math.min(bestD, maxM)) break;
      if (keepGoing && !keepGoing()) return { error: "cancelled" };
      await this.loadTile(c.t);
      const { node0, nodes } = c.t, nf = this.nflags, lo = this.lon, la = this.lat;
      for (let v = node0; v < node0 + nodes; v++) {
        if ((nf[v] & bit) === 0) continue;
        const dx = (lo[v] - plon) * kx, dy = (la[v] - plat) * ky, d = Math.sqrt(dx * dx + dy * dy);
        if (d < bestD || (d === bestD && v < best)) { bestD = d; best = v; }
      }
    }
    if (best < 0 || bestD > maxM) return { error: "nonode" };
    return { node: best, lon: this.nodeLon(best), lat: this.nodeLat(best), dist_m: bestD };
  }

  /* Tiles that meet the ellipse |p - src| + |p - dst| <= L (metres), closest
   * to the trip first (design.md section 5). */
  corridorTiles(src, dst, L) {
    const C = this.COORD;
    const lat0 = (this.lat[src] + this.lat[dst]) / 2 / C, lon0 = (this.lon[src] + this.lon[dst]) / 2 / C;
    const k = metresPerDegree(lat0);
    const X = (lon) => (lon - lon0) * k.kx, Y = (lat) => (lat - lat0) * k.ky;
    const sx = X(this.lon[src] / C), sy = Y(this.lat[src] / C), tx = X(this.lon[dst] / C), ty = Y(this.lat[dst] / C);
    const out = [], slack = L * 0.005 + 50;   // the local projection is good to ~0.5 %
    for (const t of this.tiles) {
      if (!(t.nodes > 0) || !t.bbox) continue;
      const b = t.bbox, r = [X(b[0]), Y(b[1]), X(b[2]), Y(b[3])];
      const d = rectEllipseMin(r, sx, sy, tx, ty);
      if (d <= L + slack) out.push({ t, d });
    }
    out.sort((a, b) => a.d - b.d || a.t.node0 - b.t.node0);
    return out.map((o) => o.t);
  }

  /* -------------------------------------------- route summaries (members) */
  /* One route as the page draws it: SF's summarise + geometry + resampled
   * profile + runs, with the typed arrays ready to transfer. */
  member(arcs) {
    const DM = this.DM, CM = this.CM;
    const alen = this.alen, again = this.again, aloss = this.aloss, amaxg = this.amaxg;
    const n = arcs.length, lens = new Float64Array(n), mg = new Float64Array(n), z = new Float64Array(n + 1);
    let len = 0, gain = 0, loss = 0;
    if (n) z[0] = this.elev[this.atail[arcs[0]]];
    for (let i = 0; i < n; i++) {
      const a = arcs[i];
      len += alen[a]; gain += again[a]; loss += aloss[a];
      lens[i] = alen[a]; mg[i] = amaxg[a] / this.GRADE; z[i + 1] = this.elev[this.head[a]];
    }
    const geo = this.geometry(arcs);
    return {
      length_m: len / DM, gain_m: gain / CM, loss_m: loss / CM,
      max_grade: steepestGrade(lens, z, mg, GRADE_MIN_M * DM),
      latlngs: geo.latlngs,
      profile_z: resample(this.profile(arcs), PROFILE_SAMPLES),
      runs: this.runs(arcs, geo, RUN_MIN_M),
    };
  }

  /* route geometry as [lat, lon, ...], honouring each arc's direction and
   * dropping repeated vertices; v0[i] / v1[i] are the vertex indexes where
   * arc i starts and ends */
  geometry(arcs) {
    const pts = [], tmp = [];
    const v0 = new Int32Array(arcs.length), v1 = new Int32Array(arcs.length);
    for (let i = 0; i < arcs.length; i++) {
      const a = arcs[i], e = this.aedge[a], t = this.tileOfEdge(e);
      tmp.length = 0;
      if (t && t.loaded) {
        const l = e - t.edge0;
        decodePolyline(t.geom, t.geomOff[l], t.geomOff[l + 1], tmp);
        if (this.aflags[a] & 4) {
          for (let p = 0, q = tmp.length - 2; p < q; p += 2, q -= 2) {
            const la = tmp[p], lo = tmp[p + 1]; tmp[p] = tmp[q]; tmp[p + 1] = tmp[q + 1]; tmp[q] = la; tmp[q + 1] = lo;
          }
        }
      }
      if (tmp.length < 4) {    // no geometry: a straight line between the nodes
        const u = this.atail[a], v = this.head[a];
        tmp.length = 0; tmp.push(this.nodeLat(u), this.nodeLon(u), this.nodeLat(v), this.nodeLon(v));
      }
      v0[i] = -1;
      for (let p = 0; p < tmp.length; p += 2) {
        const n = pts.length;
        if (n >= 2 && pts[n - 2] === tmp[p] && pts[n - 1] === tmp[p + 1]) {
          if (v0[i] < 0) v0[i] = n / 2 - 1;
          continue;
        }
        if (v0[i] < 0) v0[i] = n / 2;
        pts.push(tmp[p], tmp[p + 1]);
      }
      v1[i] = pts.length / 2 - 1;
    }
    return { latlngs: Float32Array.from(pts), v0, v1 };
  }

  /* elevation at every junction along the route (SF profile) */
  profile(arcs) {
    const d = new Float64Array(arcs.length + 1), z = new Float64Array(arcs.length + 1);
    if (!arcs.length) return { d: [], z: [] };
    let acc = 0;
    z[0] = this.elev[this.atail[arcs[0]]] / this.DM;
    for (let i = 0; i < arcs.length; i++) {
      acc += this.alen[arcs[i]] / this.DM;
      d[i + 1] = acc; z[i + 1] = this.elev[this.head[arcs[i]]] / this.DM;
    }
    return { d, z };
  }

  /* SF runs(u, minRun): consecutive arcs sharing a street name; unnamed and
   * short runs dropped, then neighbours with the same name re-merged. Each
   * run also carries the point halfway along it, the compass bearing there,
   * and its vertex range [i0, i1] in latlngs. */
  runs(arcs, geo, minRun) {
    const raw = [];
    let cur = null;
    for (let i = 0; i < arcs.length; i++) {
      const a = arcs[i], id = this.ename[this.aedge[a]];
      const name = id > 0 && id <= this.names.length ? this.names[id - 1] : null;
      const L = this.alen[a] / this.DM;
      if (cur && cur.name === name) { cur.last = i; cur.length_m += L; }
      else { cur = { name, first: i, last: i, length_m: L }; raw.push(cur); }
    }
    const merged = [];
    for (const r of raw) {
      if (!r.name || r.length_m < minRun) continue;
      const prev = merged[merged.length - 1];
      if (prev && prev.name === r.name) { prev.last = r.last; prev.length_m += r.length_m; }
      else merged.push({ name: r.name, first: r.first, last: r.last, length_m: r.length_m });
    }
    return merged.map((r) => {
      const i0 = geo.v0[r.first], i1 = geo.v1[r.last];
      const mb = midAndBearing(geo.latlngs, i0, i1);
      return { name: r.name, length_m: r.length_m, mid: mb.mid, bearing: mb.bearing, i0, i1 };
    });
  }
}

/* point halfway along latlngs[i0..i1] (vertex indexes) and the compass
 * bearing of the line there, degrees clockwise from north */
/* The steepest grade a route climbs over at least minLen. SF showed the
 * largest arc_maxgrade, so one 1.5 m footway piece whose ends differ by 0.5 m
 * in the terrain model read "35% steepest" on Camden Town to Highgate, where
 * nothing real is over 13%. An arc of minLen or more keeps its own steepest
 * 5 m interval (from its smoothed profile); a shorter arc counts through the
 * junction-to-junction grade of the shortest stretch of at least minLen that
 * ends with it. lens[i] is arc i's length and z[i], z[i + 1] the elevations
 * of its ends (both in 5 cm units), maxg[i] its own steepest grade. Signed
 * like SF's: negative when the route only descends. */
function steepestGrade(lens, z, maxg, minLen) {
  const n = lens.length;
  if (!n) return 0;
  const d = new Float64Array(n + 1);
  for (let i = 0; i < n; i++) d[i + 1] = d[i] + lens[i];
  let best = -Infinity, k = 0;
  for (let i = 0; i < n; i++) {
    if (lens[i] >= minLen) { if (maxg[i] > best) best = maxg[i]; continue; }
    while (d[i + 1] - d[k + 1] >= minLen) k++;
    if (d[i + 1] - d[k] < minLen) continue;  // within minLen of the start: a later stretch covers it
    const g = (z[i + 1] - z[k]) / (d[i + 1] - d[k]);
    if (g > best) best = g;
  }
  if (best === -Infinity) return d[n] > 0 ? (z[n] - z[0]) / d[n] : 0;  // shorter than minLen overall
  return best;
}

function midAndBearing(ll, i0, i1) {
  const k = metresPerDegree(ll[2 * i0]);
  let total = 0;
  for (let i = i0; i < i1; i++) {
    total += Math.hypot((ll[2 * i + 3] - ll[2 * i + 1]) * k.kx, (ll[2 * i + 2] - ll[2 * i]) * k.ky);
  }
  const half = total / 2;
  let acc = 0;
  for (let i = i0; i < i1; i++) {
    const dx = (ll[2 * i + 3] - ll[2 * i + 1]) * k.kx, dy = (ll[2 * i + 2] - ll[2 * i]) * k.ky;
    const s = Math.hypot(dx, dy);
    if (s > 0 && acc + s >= half) {
      const f = (half - acc) / s;
      const lat = ll[2 * i] + (ll[2 * i + 2] - ll[2 * i]) * f, lon = ll[2 * i + 1] + (ll[2 * i + 3] - ll[2 * i + 1]) * f;
      let brg = Math.atan2(dx, dy) * 180 / Math.PI;
      if (brg < 0) brg += 360;
      return { mid: [lat, lon], bearing: Math.round(brg * 10) / 10 };
    }
    acc += s;
  }
  return { mid: [ll[2 * i0], ll[2 * i0 + 1]], bearing: 0 };
}

/* SF resample(prof, n): piecewise linear between junction elevations, n
 * evenly spaced samples over the route's length */
function resample(prof, n) {
  const { d, z } = prof;
  const out = new Float32Array(n);
  if (!d.length) return out;
  const total = d[d.length - 1] || 1;
  let j = 0;
  for (let i = 0; i < n; i++) {
    const x = total * i / (n - 1);
    while (j < d.length - 2 && d[j + 1] < x) j++;
    const span = d[j + 1] - d[j];
    out[i] = span > 0 ? z[j] + (z[j + 1] - z[j]) * (x - d[j]) / span : z[j];
  }
  return out;
}

/* the non-dominated candidates ({g1 length, g2 climb}), by length: the
 * shorter of two equal climbs, the flatter of two equal lengths */
function frontierOnly(cands) {
  const sorted = cands.slice().sort((a, b) => a.g1 - b.g1 || a.g2 - b.g2), out = [];
  for (const c of sorted) if (!out.length || c.g2 < out[out.length - 1].g2) out.push(c);
  return out;
}

/* SF thinFrontier(members, k) on {len, gain} candidates: keep at most k,
 * spread evenly along the frontier's length in normalised (distance,
 * climbing) space, always keeping both ends; sorted by length. */
function thinFrontier(items, k) {
  const n = items.length;
  if (n <= k) return items;
  const d = items.map((m) => m.len), c = items.map((m) => m.gain);
  const dr = Math.max(1e-9, d[n - 1] - d[0]), cr = Math.max(1e-9, c[0] - c[n - 1]);
  const cum = [0];
  for (let i = 1; i < n; i++) cum.push(cum[i - 1] + Math.hypot((d[i] - d[i - 1]) / dr, (c[i] - c[i - 1]) / cr));
  const total = cum[n - 1], out = [], used = new Set();
  for (let j = 0; j < k; j++) {
    const target = total * j / (k - 1);
    let best = -1, bestErr = Infinity;
    for (let i = 0; i < n; i++) {
      if (used.has(i)) continue;
      const err = Math.abs(cum[i] - target);
      if (err < bestErr) { bestErr = err; best = i; }
    }
    used.add(best); out.push(items[best]);
  }
  return out.sort((a, b) => a.len - b.len);
}

/* ---------------------------------------------------------------- searches */
/* Scratch arrays sized to the whole graph, allocated once and reused by every
 * search (a visit stamp for A*, a fill for the bound arrays). Searches are
 * objects with step(deadline) -> done, run in slices by the caller. */
class Router {
  constructor(g) {
    this.g = g;
    const n = g.n;
    this.dist = new Float64Array(n); this.prev = new Int32Array(n); this.seen = new Int32Array(n);
    this.stamp = 0;
    this.h1 = new Int32Array(n); this.h2 = new Int32Array(n); this.g2min = new Int32Array(n);
    this.heap = new MinHeap();
    this.rIndptr = new Int32Array(n + 1); this.rArcs = new Int32Array(0); this.revVersion = -1;
    this.lcap = 1 << 16;
    this.newLabels(this.lcap);
  }
  newLabels(cap) {
    this.lcap = cap;
    this.lG1 = new Int32Array(cap); this.lG2 = new Int32Array(cap);
    this.lParent = new Int32Array(cap); this.lArc = new Int32Array(cap);
  }
  /* give back the memory of a very large search */
  release() {
    if (this.lcap > (1 << 20)) this.newLabels(1 << 16);
    this.heap.shrink(1 << 16);
  }

  /* Single-objective search on length + alpha * climbing (SF's cost with class
   * multipliers off) in integer 5 cm units: arc_len + alpha * DM / CM *
   * arc_gain. A*, with the straight-line bound of H_FACTOR / H_MARGIN_M, which
   * is admissible but at the centimetre level not quite consistent, so a node
   * is re-opened whenever a cheaper path to it turns up; the first time dst
   * leaves the heap its cost is optimal. Plain Dijkstra (h = 0) when the
   * loaded tiles fail the chord check. */
  shortest(src, dst, bit, alpha) {
    const g = this.g, lon = g.lon, lat = g.lat, nflags = g.nflags, indptr = g.indptr, head = g.head;
    const alen = g.alen, again = g.again, aflags = g.aflags;
    const dist = this.dist, prev = this.prev, seen = this.seen, heap = this.heap;
    const stamp = ++this.stamp;
    const ga = alpha * g.DM / g.CM;
    const k = metresPerDegree((lat[src] + lat[dst]) / 2 / g.COORD), f = g.straightBounds ? H_FACTOR : 0;
    const kx = f * k.kx * g.DM / g.COORD, ky = f * k.ky * g.DM / g.COORD, hm = H_MARGIN_M * g.DM;
    const dlon = lon[dst], dlat = lat[dst];
    const h = (v) => {
      const dx = (lon[v] - dlon) * kx, dy = (lat[v] - dlat) * ky, e = Math.sqrt(dx * dx + dy * dy) - hm;
      return e > 0 ? e : 0;
    };
    heap.reset();
    seen[src] = stamp; dist[src] = 0; prev[src] = -1; heap.push(h(src), src);
    const st = { done: false, found: false, settled: 0, arcs: null, cost: Infinity };
    st.step = (deadline) => {
      let it = 0;
      while (heap.n > 0) {
        if ((++it & 511) === 0 && now() > deadline) return false;
        const u = heap.pop(), du = dist[u];
        if (heap.topKey > du + h(u)) continue;      // superseded by a cheaper path
        st.settled++;
        if (u === dst) { st.found = true; break; }
        for (let a = indptr[u], e = indptr[u + 1]; a < e; a++) {
          if ((aflags[a] & bit) === 0) continue;
          const v = head[a];
          if ((nflags[v] & bit) === 0) continue;  // other mode's component, or tile not loaded
          const nd = du + alen[a] + ga * again[a];
          if (seen[v] !== stamp || nd < dist[v]) {
            seen[v] = stamp; dist[v] = nd; prev[v] = a;
            heap.push(nd + h(v), v);
          }
        }
      }
      st.done = true;
      if (st.found) { st.cost = dist[dst]; st.arcs = this.trace(src, dst); }
      return true;
    };
    return st;
  }

  trace(src, dst) {
    const arcs = [], prev = this.prev, atail = this.g.atail;
    let v = dst, guard = 0;
    while (v !== src) {
      const a = prev[v];
      if (a < 0 || guard++ > this.g.n) return null;
      arcs.push(a); v = atail[a];
    }
    return arcs.reverse();
  }

  /* reverse adjacency over the loaded tiles' arcs (incoming arcs by head, in
   * arc order), rebuilt only when tiles have landed since the last build */
  buildReverse() {
    const g = this.g;
    if (this.revVersion === g.version) return;
    const n = g.n, head = g.head, rp = this.rIndptr;
    rp.fill(0);
    const tiles = g.loaded.slice().sort((a, b) => a.arc0 - b.arc0);
    let m = 0;
    for (const t of tiles) {
      for (let a = t.arc0, e = t.arc0 + t.arcs; a < e; a++) rp[head[a] + 1]++;
      m += t.arcs;
    }
    for (let i = 0; i < n; i++) rp[i + 1] += rp[i];
    if (this.rArcs.length < m) this.rArcs = new Int32Array(Math.ceil(m * 1.25));
    const ra = this.rArcs;
    for (const t of tiles) {
      for (let a = t.arc0, e = t.arc0 + t.arcs; a < e; a++) ra[rp[head[a]]++] = a;
    }
    for (let i = n; i > 0; i--) rp[i] = rp[i - 1];
    rp[0] = 0;
    this.revVersion = g.version;
  }

  /* Exact lower bound from every node to dst on one per-arc weight (a reverse
   * Dijkstra, SF boundsTo) over the loaded tiles, in the weight's own integer
   * units, written to out (INF where unknown). Nodes whose bound exceeds cap
   * are left at INF. With src >= 0, a node is also left out when even a
   * straight line from src plus its bound exceeds cap (outside the cap
   * ellipse); with restrict, only nodes with a finite restrict[] are used. */
  bounds(dst, bit, weight, out, cap, restrict, src) {
    const g = this.g, nflags = g.nflags, aflags = g.aflags, atail = g.atail;
    const rp = this.rIndptr, ra = this.rArcs, heap = this.heap;
    const lon = g.lon, lat = g.lat;
    const useLb = src >= 0 && g.straightBounds;
    let kx = 0, ky = 0, slon = 0, slat = 0;
    const hm = H_MARGIN_M * g.DM;
    if (useLb) {
      const k = metresPerDegree((lat[src] + lat[dst]) / 2 / g.COORD);
      kx = H_FACTOR * k.kx * g.DM / g.COORD; ky = H_FACTOR * k.ky * g.DM / g.COORD;
      slon = lon[src]; slat = lat[src];
    }
    out.fill(INF);
    heap.reset();
    out[dst] = 0; heap.push(0, dst);
    const st = { done: false, settled: 0 };
    st.step = (deadline) => {
      let it = 0;
      while (heap.n > 0) {
        if ((++it & 511) === 0 && now() > deadline) return false;
        const u = heap.pop(), du = heap.topKey;
        if (du > out[u]) continue;
        st.settled++;
        for (let k = rp[u], e = rp[u + 1]; k < e; k++) {
          const a = ra[k];
          if ((aflags[a] & bit) === 0) continue;
          const v = atail[a];
          if ((nflags[v] & bit) === 0) continue;
          if (restrict !== null && restrict[v] >= INF) continue;
          const nd = du + weight[a];
          if (nd >= out[v] || nd > cap) continue;
          if (useLb) {
            const dx = (lon[v] - slon) * kx, dy = (lat[v] - slat) * ky, lb = Math.sqrt(dx * dx + dy * dy) - hm;
            if (nd + (lb > 0 ? lb : 0) > cap) continue;
          }
          out[v] = nd; heap.push(nd, v);
        }
      }
      st.done = true;
      return true;
    };
    return st;
  }

  /* BOA*, exactly as SF engine.js pareto(): labels (node, length, climb)
   * expand in lexicographic order of (length + h1, climb + h2); a label is
   * dropped at a node unless it climbs at least epsNode less than every label
   * expanded there before (eps at dst), and globally unless its optimistic
   * climb beats the best solution so far by eps. dCap (5 cm units) and gCap
   * (cm) bound length and climbing. h1 / h2 must already hold the bounds.
   * A label is 16 bytes (its node is the head of its arc, or src).
   * London: every o.adaptEvery labels o.adapt(search) may raise search.eps /
   * search.epsNode (raising only prunes more: every solution is still a real
   * path and successive solutions still differ by at least eps). maxLabels
   * stops the search at the short end of the frontier (truncated). */
  pareto(src, dst, bit, o) {
    const g = this.g, indptr = g.indptr, head = g.head, alen = g.alen, again = g.again;
    const aflags = g.aflags, nflags = g.nflags;
    const h1 = this.h1, h2 = this.h2, g2min = this.g2min, heap = this.heap;
    const dCap = o.dCap, gCap = o.gCap, maxLabels = o.maxLabels || 4e6;
    const K = HEAP_KEY_BASE;
    g2min.fill(INF);
    heap.reset();
    let cap = this.lcap, lG1 = this.lG1, lG2 = this.lG2, lParent = this.lParent, lArc = this.lArc;
    let nl = 0;
    const grow = () => {
      cap *= 2;
      const r = (old) => { const a = new Int32Array(cap); a.set(old); return a; };
      lG1 = r(lG1); lG2 = r(lG2); lParent = r(lParent); lArc = r(lArc);
      this.lcap = cap; this.lG1 = lG1; this.lG2 = lG2; this.lParent = lParent; this.lArc = lArc;
    };
    const add = (node, g1, g2, parent, arc) => {
      if (nl === cap) grow();
      lG1[nl] = g1; lG2[nl] = g2; lParent[nl] = parent; lArc[nl] = arc;
      heap.push((g1 + h1[node]) * K + Math.min(g2 + h2[node], K - 1), nl);
      nl++;
    };
    const search = {
      solutions: [], done: false, expanded: 0, labels: 0, truncated: false, reason: null, adapted: 0,
      eps: o.eps, epsNode: o.epsNode, f1start: h1[src], dCap, reached: 0,
    };
    /* share of the length range [shortest, dCap] the search has passed: the
     * f1 of the next label (f1 never decreases, the bounds are consistent) */
    search.progress = () => {
      if (search.done && !search.truncated) return 1;
      if (heap.n === 0) return search.done ? search.reached : 1;
      const f1 = Math.floor(heap.k[0] / K), span = dCap - search.f1start;
      return span > 0 ? Math.max(0, Math.min(1, (f1 - search.f1start) / span)) : 1;
    };
    if (src === dst || h1[src] >= INF) { search.done = true; search.step = () => true; return search; }
    add(src, 0, 0, -1, -1);
    const adaptEvery = o.adaptEvery || (1 << 16);
    let nextCheck = adaptEvery;
    search.stop = (reason) => {
      search.reached = search.progress();
      search.truncated = true; search.reason = reason; search.labels = nl; search.done = true;
    };
    search.step = (deadline) => {
      let eps = search.eps, epsNode = search.epsNode;
      let it = 0;
      while (heap.n > 0) {
        if ((++it & 1023) === 0 && now() > deadline) { search.labels = nl; return false; }
        const x = heap.pop();
        const ar = lArc[x], node = ar < 0 ? src : head[ar], g1 = lG1[x], g2 = lG2[x];
        if (g2 + (node === dst ? eps : epsNode) > g2min[node] || g2 + h2[node] + eps > g2min[dst]) continue;
        g2min[node] = g2;
        search.expanded++;
        if (node === dst) { search.solutions.push({ x, g1, g2 }); continue; }
        for (let a = indptr[node], e = indptr[node + 1]; a < e; a++) {
          if ((aflags[a] & bit) === 0) continue;
          const v = head[a];
          if ((nflags[v] & bit) === 0) continue;
          const n1 = g1 + alen[a], n2 = g2 + again[a], b2 = h2[v];
          if (n1 + h1[v] > dCap || n2 + b2 > gCap) continue;
          if (n2 + epsNode > g2min[v] || n2 + b2 + eps > g2min[dst]) continue;
          add(v, n1, n2, x, a);
        }
        if (nl > maxLabels) { search.stop("labels"); return true; }
        if (nl >= nextCheck) {
          nextCheck = nl + adaptEvery;
          if (o.adapt) { search.labels = nl; o.adapt(search); eps = search.eps; epsNode = search.epsNode; }
        }
      }
      search.labels = nl;
      search.done = true;
      return true;
    };
    return search;
  }

  /* arcs of the path that ends in label x (labels live until the next search) */
  labelPath(x) {
    const arcs = [], lParent = this.lParent, lArc = this.lArc;
    for (let y = x; lParent[y] >= 0; y = lParent[y]) arcs.push(lArc[y]);
    return arcs.reverse();
  }
}

/* The BOA* label budget (London): every adapt_every labels, project the
 * final label count from the rate since the last change and the share of the
 * length range covered; while it heads past `target`, double epsNode up to
 * eps, then both up to epsMax (so routes closer than epsMax in climbing are
 * merged: invisible once thinned to MAX_ROUTES), then epsNode alone up to
 * 2 epsMax. It reads label counts, never the clock, so a trip gives the same
 * family on every machine; past that, max_labels and frontier_ms truncate. */
function labelBudget(target, epsMax, every) {
  let q0 = 0, l0 = 0;
  return (s) => {
    const q = s.progress(), dq = q - q0, dl = s.labels - l0;
    if (dl < every / 2 || (dq < 0.01 && dl < target / 4)) return;   // too early to tell
    const projected = dq > 0 ? s.labels + dl / dq * (1 - q) : Infinity;
    if (projected <= target) return;
    if (s.epsNode < s.eps) s.epsNode = Math.min(s.eps, s.epsNode * 2);
    else if (s.eps < epsMax) s.eps = s.epsNode = Math.min(epsMax, s.eps * 2);
    else if (s.epsNode < 2 * epsMax) s.epsNode = Math.min(2 * epsMax, s.epsNode * 2);
    else return;
    s.adapted++;
    q0 = q; l0 = s.labels;
  };
}

/* ---------------------------------------------------------------- the worker */
const W = {
  graph: null, router: null, ready: null, epoch: 0,
  latestGen: -Infinity, cancelledGen: -Infinity,
  tuning: Object.assign({}, TUNING_DEFAULTS),
  fetch: (url, init) => fetch(url, init),
  post: (msg, transfer) => self.postMessage(msg, transfer || []),
};
const CANCELLED = { cancelled: true };

/* a task boundary that lets queued messages (cancel, a newer route) in;
 * MessageChannel avoids the 4 ms clamp of nested setTimeout(0) */
const yieldTask = (() => {
  if (typeof setImmediate === "function") return () => new Promise((r) => setImmediate(r));
  if (typeof MessageChannel === "function") {
    const ch = new MessageChannel(), queue = [];
    ch.port1.onmessage = () => { const r = queue.shift(); if (r) r(); };
    return () => new Promise((r) => { queue.push(r); ch.port2.postMessage(0); });
  }
  return () => new Promise((r) => setTimeout(r, 0));
})();

function makeJob(gen) {
  const epoch = W.epoch;
  const job = {
    gen,
    live: () => epoch === W.epoch && gen === W.latestGen && gen > W.cancelledGen,
    alive: () => { if (!job.live()) throw CANCELLED; },
    lastProgress: -Infinity,
  };
  return job;
}

/* run a search to completion in slices, yielding between them */
async function sliced(job, st) {
  for (;;) {
    job.alive();
    if (st.step(now() + W.tuning.slice_ms)) return st;
    await yieldTask();
  }
}

function progress(job, stage, done, total, extra, force) {
  const t = now();
  if (!force && t - job.lastProgress < W.tuning.progress_ms) return;
  job.lastProgress = t;
  W.post(Object.assign({ type: "progress", gen: job.gen, stage, done, total }, extra || {}));
}

function fail(gen, code, message) {
  W.post({ type: "error", gen, code, message });
}

/* an exception as a protocol error: a hashed file that 404s (a deploy landed
 * mid-session) is code "internal" with stale: true and "(404)" in the message */
function errorOf(e) {
  const out = { code: "internal", message: String((e && e.message) || e) };
  if (e && e.status) out.status = e.status;
  if (e && e.status === 404) out.stale = true;
  return out;
}

function postFamily(gen, partial, truncated, members, ends, info) {
  const transfer = [];
  for (const m of members) transfer.push(m.latlngs.buffer, m.profile_z.buffer);
  W.post({ type: "family", gen, partial, truncated, members, ends, info }, transfer);
}

async function init(msg) {
  W.epoch++;
  const epoch = W.epoch;
  W.graph = null; W.router = null;
  W.tuning = Object.assign({}, TUNING_DEFAULTS, msg.tuning || {});
  const here = typeof location !== "undefined" ? location.href : undefined;
  const indexURL = new URL(msg.index_url, here).href;
  const res = await W.fetch(indexURL);
  if (!res.ok) throw new HttpError(indexURL, res.status);
  const index = JSON.parse(UTF8.decode(await inflateBytes(new Uint8Array(await res.arrayBuffer()))));
  if (epoch !== W.epoch) return;
  // tile URLs are relative to the site root, the index's parent's parent
  const base = msg.base_url ? new URL(msg.base_url, here).href : new URL("../", indexURL).href;
  const meta = index.meta || {};
  if (meta.alpha_max > 0) ALPHA_MAX = meta.alpha_max;
  if (meta.eps_gain_cm > 0) EPS_GAIN_CM = meta.eps_gain_cm;
  if (meta.eps_node_cm > 0) EPS_NODE_CM = meta.eps_node_cm;
  if (meta.max_routes > 0) MAX_ROUTES = meta.max_routes;
  const g = new TiledGraph(index, base, W.fetch);
  W.graph = g;
  W.router = new Router(g);
  g.loadNames(index.names).catch(() => { g.names = []; });   // runs then carry no names
  W.post({ type: "ready", meta, release: index.release || null });
}

async function graphReady(epoch) {
  await W.ready;
  if (epoch !== W.epoch || !W.graph) throw CANCELLED;
  return W.graph;
}

async function onSnap(msg) {
  const epoch = W.epoch;
  try {
    if (!W.ready) throw new Error("the worker has no index yet (send init first)");
    const g = await graphReady(epoch);
    if (msg.mode !== "walk" && msg.mode !== "bike") throw new Error("unknown mode " + JSON.stringify(msg.mode));
    const bit = msg.mode === "bike" ? 2 : 1;
    const r = await g.snap(+msg.lon, +msg.lat, bit, W.tuning.snap_max_m, () => epoch === W.epoch, W.tuning.snap_prefetch_m);
    if (epoch !== W.epoch) return;
    if (r.error) { W.post({ type: "snapped", id: msg.id, error: r.error }); return; }
    W.post({ type: "snapped", id: msg.id, node: r.node, lon: r.lon, lat: r.lat, dist_m: r.dist_m });
  } catch (e) {
    if (e === CANCELLED || epoch !== W.epoch) return;
    const err = errorOf(e);
    W.post({ type: "snapped", id: msg.id, error: err.code, stale: err.stale, message: err.message });
  }
}

/* an endpoint's node in this mode: the page's node when it has the mode bit,
 * else the nearest node with it */
async function endpoint(job, p, bit) {
  const g = W.graph;
  if (!p) return -1;
  if (Number.isInteger(p.node) && p.node >= 0 && p.node < g.n) {
    const t = g.tileOfNode(p.node);
    if (t) {
      await g.loadTile(t);
      if (g.nflags[p.node] & bit) return p.node;
    }
  }
  if (!Number.isFinite(p.lon) || !Number.isFinite(p.lat)) return -1;
  const r = await g.snap(p.lon, p.lat, bit, W.tuning.snap_max_m, job.live, W.tuning.snap_prefetch_m);
  return r.error ? -1 : r.node;
}

async function loadCorridor(job, src, dst, L, info) {
  const g = W.graph;
  const list = g.corridorTiles(src, dst, L).filter((t) => !t.loaded);
  if (!list.length) return 0;
  const total = list.reduce((s, t) => s + (t.bytes || 1), 0);
  let done = 0;
  progress(job, "tiles", 0, total, null, true);
  const t0 = now();
  await g.loadTiles(list, W.tuning.fetch_concurrency, (t) => {
    done += t.bytes || 1;
    if (job.live()) progress(job, "tiles", done, total, null, done === total);
  }, job.live);
  job.alive();
  info.tiles_fetched += list.length; info.tile_bytes += total; info.ms.tiles += now() - t0;
  return list.length;
}

async function runShortest(job, src, dst, bit, alpha, info) {
  const g = W.graph, t0 = now();
  const st = await sliced(job, W.router.shortest(src, dst, bit, alpha));
  if (alpha === 0 || alpha === ALPHA_MAX) info.ms[alpha ? "flattest" : "shortest"] += now() - t0;
  info.settled.push(st.settled);
  if (!st.found) return null;
  let g1 = 0, g2 = 0;
  for (const a of st.arcs) { g1 += g.alen[a]; g2 += g.again[a]; }
  return { arcs: st.arcs, g1, g2 };
}

/* A truncated frontier is its short end only. Bridge the gap to the
 * flattest route with the routes minimising length + alpha x climbing for a
 * few alphas between the frontier's slope where it stopped and ALPHA_MAX
 * (geometric steps): each is a true frontier point. */
async function bridge(job, src, dst, bit, S, F, last, info) {
  const g = W.graph, k = W.tuning.bridge_routes, out = [];
  if (!(k > 0)) return out;
  const dL = (last.g1 - S.g1) / g.DM, dG = (S.g2 - last.g2) / g.CM;
  const a0 = Math.min(ALPHA_MAX / 2, Math.max(1, dG > 0 ? dL / dG : 1));
  const r = Math.pow(ALPHA_MAX / a0, 1 / (k + 1));
  for (let i = 1; i <= k; i++) {
    const B = await runShortest(job, src, dst, bit, Math.round(a0 * Math.pow(r, i)), info);
    if (B && B.g1 > last.g1 && B.g2 < last.g2 && B.g2 > F.g2) out.push(B);
  }
  info.bridged = out.length;
  return out;
}

function sameArcs(a, b) {
  return a.length === b.length && a.every((x, i) => x === b[i]);
}

async function onRoute(msg) {
  const gen = msg.gen;
  const job = makeJob(gen);
  const T0 = now();
  const info = {
    tiles_fetched: 0, tile_bytes: 0, corridor_m: 0, rounds: 0, settled: [],
    labels: 0, expanded: 0, solutions: 0, eps_gain_cm: 0, eps_node_cm: 0,
    ms: { tiles: 0, shortest: 0, flattest: 0, bounds: 0, frontier: 0, total: 0 },
  };
  try {
    job.alive();
    if (!W.ready) return fail(gen, "internal", "the worker has no index yet (send init first)");
    await graphReady(W.epoch);
    job.alive();
    const g = W.graph, R = W.router, T = W.tuning;
    // SF routed any unknown mode as a fewest-arcs walk (spec 01, 4.2): refuse it
    if (msg.mode !== "walk" && msg.mode !== "bike") return fail(gen, "internal", "unknown mode " + JSON.stringify(msg.mode));
    const mode = msg.mode, bit = mode === "bike" ? 2 : 1;
    const noRoute = () => fail(gen, mode === "bike" ? "nobike" : "unreachable",
      mode === "bike" ? "No bikeable route between those points." : "No route between those points.");
    const picked = await Promise.all([endpoint(job, msg.from, bit), endpoint(job, msg.to, bit)]);
    job.alive();
    const src = picked[0], dst = picked[1];
    if (src < 0 || dst < 0) return noRoute();
    if (src === dst) return fail(gen, "same", "Those are the same junction.");

    // the corridor: grow it while the flattest route runs close to its edge
    const D = g.nodeDist(src, dst);
    let L = Math.max(1.35 * D + 2000, D + 3000), S = null, F = null;
    for (let round = 0, Lprev = 0; ; round++) {
      info.rounds = round + 1; info.corridor_m = Math.round(L);
      const fresh = await loadCorridor(job, src, dst, L, info);
      if (round > 0 && fresh === 0 && S) break;          // nothing new: the routes stand
      if (round === 0 || fresh > 0) {
        // a shortest route no longer than the last corridor's L lies inside
        // it, so it is already the shortest anywhere
        if (!S || S.g1 / g.DM > Lprev) S = await runShortest(job, src, dst, bit, 0, info);
        if (S) F = (await runShortest(job, src, dst, bit, ALPHA_MAX, info)) || S;
      }
      Lprev = L;
      if (!S) {
        if (round < T.grow_rounds) { L *= 1.6; continue; }
        return noRoute();
      }
      if (F.g1 / g.DM > 0.9 * L && round < T.grow_rounds) { L = 1.15 * F.g1 / g.DM; continue; }
      break;
    }
    await g.namesPromise.catch(() => {});
    job.alive();

    // shortest and flattest go up at once; the frontier fills in between
    const ends = [src, dst].map((v) => ({ node: v, lon: g.nodeLon(v), lat: g.nodeLat(v) }));
    const same = sameArcs(S.arcs, F.arcs);
    postFamily(gen, true, false, same ? [g.member(S.arcs)] : [g.member(S.arcs), g.member(F.arcs)], ends,
      { ms: Object.assign({}, info.ms, { total: now() - T0 }) });

    // bounds over the loaded tiles, cut at the caps
    const dCap = F.g1, gCap = S.g2;
    let t0 = now();
    R.buildReverse();
    await sliced(job, R.bounds(dst, bit, g.alen, R.h1, dCap, null, src));
    await sliced(job, R.bounds(dst, bit, g.again, R.h2, gCap, R.h1, -1));
    info.ms.bounds = now() - t0;

    // BOA* with SF's tolerances, raised only if the label count says so
    const epsMax = Math.max(EPS_GAIN_CM, Math.round(Math.max(0, gCap - F.g2) / T.eps_frac));
    const search = R.pareto(src, dst, bit, {
      eps: EPS_GAIN_CM, epsNode: Math.min(EPS_NODE_CM, EPS_GAIN_CM), dCap, gCap, maxLabels: T.max_labels,
      adapt: labelBudget(T.label_target, epsMax, T.adapt_every), adaptEvery: T.adapt_every,
    });
    t0 = now();
    progress(job, "frontier", 0, 1000, { solutions: 0 }, true);
    for (;;) {
      job.alive();
      if (search.step(now() + T.slice_ms)) break;
      if (now() - t0 > T.frontier_ms) { search.stop("time"); break; }
      progress(job, "frontier", Math.round(1000 * search.progress()), 1000, { solutions: search.solutions.length });
      await yieldTask();
    }
    info.ms.frontier = now() - t0;
    info.labels = search.labels; info.expanded = search.expanded; info.solutions = search.solutions.length;
    info.eps_gain_cm = search.eps; info.eps_node_cm = search.epsNode; info.eps_raised = search.adapted;
    if (search.truncated) { info.truncated = search.reason; info.reached = Math.round(1000 * search.reached) / 1000; }

    // finishFamily, thinned on (length, climbing) before building members
    let cands = search.solutions.map((s) => ({ g1: s.g1, g2: s.g2, x: s.x, arcs: null }));
    if (!cands.length) cands = [{ g1: S.g1, g2: S.g2, arcs: S.arcs }];
    const last = cands[cands.length - 1];
    if (search.truncated && F.g2 < last.g2) {
      t0 = now();
      cands = cands.concat(await bridge(job, src, dst, bit, S, F, last, info));
      info.ms.bridge = now() - t0;
    }
    // the weighted flattest route closes the family when tolerances or
    // truncation left it out; then drop anything dominated
    cands.push({ g1: F.g1, g2: F.g2, arcs: F.arcs });
    cands = frontierOnly(cands);
    for (const c of cands) { c.len = c.g1 / g.DM; c.gain = c.g2 / g.CM; }
    const kept = thinFrontier(cands, MAX_ROUTES);
    for (const c of kept) if (!c.arcs) c.arcs = R.labelPath(c.x);
    R.release();
    const members = kept.map((c) => g.member(c.arcs));
    progress(job, "frontier", 1000, 1000, { solutions: search.solutions.length }, true);
    info.ms.total = now() - T0;
    postFamily(gen, false, search.truncated, members, ends, info);
  } catch (e) {
    if (e === CANCELLED || !job.live()) return;
    W.post(Object.assign({ type: "error", gen }, errorOf(e)));
  }
}

function onMessage(ev) {
  const msg = (ev && ev.data) || {};
  switch (msg.type) {
    case "init":
      W.ready = init(msg);
      // gen -1: not about any route, so the page shows it whatever it is doing
      W.ready.catch((e) => { W.post(Object.assign({ type: "error", gen: -1, init: true }, errorOf(e))); });
      break;
    case "snap":
      onSnap(msg);
      break;
    case "route":
      if (msg.gen > W.latestGen) W.latestGen = msg.gen;   // generation ids only grow
      onRoute(msg);
      break;
    case "cancel":
      if (msg.gen > W.cancelledGen) W.cancelledGen = msg.gen;
      break;
    default:
      break;
  }
}

if (typeof self !== "undefined") {
  self.onmessage = onMessage;
  // for tests and the console; nothing in the page reads it
  self.FlattenWorker = {
    W, TiledGraph, Router, MinHeap, inflateBytes, parseFLT1, decodePolyline, metresPerDegree,
    rectEllipseMin, segmentHitsRect, thinFrontier, resample, midAndBearing, steepestGrade, onMessage, INF,
    TUNING_DEFAULTS,
  };
}
