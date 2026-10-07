/* Flatten London: the route finder page.
 *
 * Adapted from flattensf (MIT) by Drew Edwards: sf_flat_routes/web/simple.js.
 * Same card, slider, stats, profile, family lines and share links; what
 * changes is scale. San Francisco shipped its whole graph in one bundle and
 * routed on the main thread. London is about twelve times bigger, so:
 *
 *   - a Web Worker (worker.js) owns the graph tiles, snapping and routing,
 *     and talks to this page through the protocol in docs/design.md 5.1;
 *     every route request carries a generation id and stale answers are
 *     dropped, so the page never blocks on routing;
 *   - the map is a raster basemap (hillshade, water, streets up to z13)
 *     with the streets drawn as vectors from the graph tiles in view above
 *     that, and map labels culled for collisions;
 *   - place search is an offline index (stations, areas, streets,
 *     junctions, places) loaded on first focus, plus postcodes, with a
 *     token prefix index instead of a scan per keystroke;
 *   - distances are metric by default with a km/mi toggle.
 *
 * The top half of this file is pure (no DOM) and is exported for the Node
 * tests in tests/test_site.py; the App below it only runs in a page that
 * defines window.FLR = {index_url, worker_url}.
 */
"use strict";

(function (root) {
  /* =============================================================== core */
  const MI = 1609.344, FT = 3.28084, KM = 1000;
  const clamp = (v, a, b) => Math.min(b, Math.max(a, v));
  const lerp = (a, b, t) => a + (b - a) * t;
  const ease = (t) => 1 - Math.pow(1 - t, 3);

  function hexToRgb(h) {
    h = String(h).trim().replace("#", "");
    if (h.length === 3) h = h.split("").map((c) => c + c).join("");
    const n = parseInt(h, 16);
    return [(n >> 16) & 255, (n >> 8) & 255, n & 255];
  }
  /* three-stop ramp, shortest -> middle -> flattest, matching the slider */
  function rampOf(stops, t) {
    const s = stops.map(hexToRgb);
    const x = clamp(t, 0, 1) * 2, i = Math.min(1, Math.floor(x)), k = x - i;
    return "rgb(" + s[i].map((v, c) => Math.round(lerp(v, s[i + 1][c], k))).join(",") + ")";
  }

  /* ---------------------------------------------------------------- units */
  const num = (v) => Math.round(v).toLocaleString("en-GB");
  function makeUnits(system) {
    if (system === "imperial") {
      return {
        system,
        dist: (m) => (m / MI < 10 ? (m / MI).toFixed(1) : Math.round(m / MI)) + "<small>mi</small>",
        climb: (m) => num(m * FT) + "<small>ft</small>",
        deltaDist: (m) => "+" + (m / MI).toFixed(1) + " mi",
        deltaClimb: (m) => "−" + num(m * FT) + " ft",
        elev: (m) => Math.round(m * FT) + " ft",
        span: (m) => (m / MI).toFixed(1) + " mi",
      };
    }
    return {
      system: "metric",
      dist: (m) => (m / KM < 10 ? (m / KM).toFixed(1) : Math.round(m / KM)) + "<small>km</small>",
      climb: (m) => num(m) + "<small>m</small>",
      deltaDist: (m) => "+" + (m / KM).toFixed(1) + " km",
      deltaClimb: (m) => "−" + num(m) + " m",
      elev: (m) => Math.round(m) + " m",
      span: (m) => (m / KM).toFixed(1) + " km",
    };
  }
  const fmtPct = (g) => (g * 100).toFixed(g * 100 < 10 ? 1 : 0) + "<small>%</small>";

  /* -------------------------------------------------------- text matching */
  /* Street-type words collapse to their abbreviations on both the index and
   * the query, so "Camden High St", "Camden High Street" and "camden high"
   * all match. UK forms added to SF's list; both directions are normalised,
   * so these are synonyms, not rewrites of what the user sees. */
  const ABBREV = { street: "st", avenue: "ave", av: "ave", boulevard: "blvd", drive: "dr", road: "rd",
    court: "ct", place: "pl", lane: "ln", la: "ln", terrace: "ter", terr: "ter", highway: "hwy",
    parkway: "pkwy", circle: "cir", alley: "aly", square: "sq", stairway: "stwy", stairs: "stwy",
    way: "wy", north: "n", south: "s", east: "e", west: "w", saint: "st", mount: "mt",
    gardens: "gdns", crescent: "cres", close: "cl", grove: "gr", parade: "pde", great: "gt",
    upper: "upr", lower: "lwr", green: "grn", embankment: "emb" };
  /* abbreviation -> the full words it stands for (st: street, saint) */
  const EXPAND = {};
  for (const [full, ab] of Object.entries(ABBREV)) {
    if (full.length <= ab.length) continue;
    (EXPAND[ab] = EXPAND[ab] || []).push(full);
  }
  const ABBREV_KEYS = Object.keys(EXPAND);
  const _abForPrefix = new Map();
  /* the abbreviations whose expansion starts with a partly typed word:
   * "gre" -> ["grn", "gt"], so "Bethnal Gre" still finds "Bethnal Green" */
  function abbrevsFor(t) {
    let out = _abForPrefix.get(t);
    if (out) return out;
    out = ABBREV_KEYS.filter((a) => a !== t && EXPAND[a].some((w) => w.startsWith(t)));
    _abForPrefix.set(t, out);
    return out;
  }
  /* lower case, no accents or apostrophes, punctuation to spaces */
  function words(s) {
    const t = String(s).normalize("NFD").replace(/\p{M}/gu, "").toLowerCase()
      .replace(/[’']/g, "")
      .replace(/[^\p{L}\p{N}\s]/gu, " ")
      .replace(/\s+/g, " ").trim();
    return t ? t.split(" ") : [];
  }
  const norm = (s) => words(s).map((w) => ABBREV[w] || w).join(" ");

  /* The query side of norm: every word is abbreviated except the last one
   * while it may still be half typed (no trailing space), which is matched
   * as a prefix of a word or of its expansion instead. */
  function parseQuery(raw) {
    const w = words(raw);
    const partial = w.length > 0 && !/\s$/.test(raw);
    const toks = w.map((x, i) => (partial && i === w.length - 1) ? x : (ABBREV[x] || x));
    const qa = w.map((x) => ABBREV[x] || x).join(" ");
    return { toks, partial, q: toks.join(" "), qa };
  }
  /* does t start a word of hay (or, for a partial word, an abbreviated word whose expansion it starts)? */
  function wordPrefix(hay, t, partial) {
    if ((" " + hay).includes(" " + t)) return true;
    if (!partial) return false;
    const padded = " " + hay + " ";
    for (const a of abbrevsFor(t)) if (padded.includes(" " + a + " ")) return true;
    return false;
  }
  function startsWithWords(nn, prefix) {
    return nn === prefix || nn.startsWith(prefix + " ");
  }

  /* -------------------------------------------------------- search index */
  /* search.json (design 3.4) is columnar: name, kind, loc, lon, lat, rank.
   * The index is a sorted table of every distinct word with the entries
   * that contain it (CSR postings), so a query only looks at the entries
   * under its rarest word. */
  class SearchIndex {
    constructor(data) {
      this.kinds = data.kinds || [];
      this.localities = data.localities || [];
      this.name = data.name; this.kind = data.kind; this.loc = data.loc || [];
      this.lon = data.lon; this.lat = data.lat; this.rank = data.rank || [];
      this.n = this.name.length;
      this.locNorm = this.localities.map(norm);
      this.J = this.kinds.indexOf("junction");
      this.S = this.kinds.indexOf("street");
      this.ready = false;
      this._halves = new Map();
      this.buildSpatial();
    }
    /* "High Street, Hampton"; no locality when the name already says it ("Highgate Village") */
    display(i) {
      const l = this.loc[i], name = this.name[i];
      if (!(l >= 0) || !this.localities[l]) return name;
      if ((" " + norm(name) + " ").includes(" " + this.locNorm[l] + " ")) return name;
      return name + ", " + this.localities[l];
    }
    /* junctions and streets on a ~300 m grid, for naming a dropped pin */
    buildSpatial() {
      const cells = new Map(), CY = 0.003, CX = 0.0048;
      for (let i = 0; i < this.n; i++) {
        const k = this.kind[i];
        if (k !== this.J && k !== this.S) continue;
        const key = Math.floor(this.lon[i] / 1e6 / CX) + ":" + Math.floor(this.lat[i] / 1e6 / CY);
        let c = cells.get(key);
        if (!c) cells.set(key, c = []);
        c.push(i);
      }
      this.cells = cells; this.CX = CX; this.CY = CY;
    }
    /* nearest junction within maxM metres, else nearest street, else -1 */
    nearest(lon, lat, maxM = 400) {
      const cx = Math.floor(lon / this.CX), cy = Math.floor(lat / this.CY);
      const kx = 111320 * Math.cos(lat * Math.PI / 180), ky = 110540;
      let best = [-1, -1], bestD = [maxM * maxM, maxM * maxM];
      for (let dx = -2; dx <= 2; dx++) {
        for (let dy = -2; dy <= 2; dy++) {
          const c = this.cells.get((cx + dx) + ":" + (cy + dy));
          if (!c) continue;
          for (const i of c) {
            const ex = (this.lon[i] / 1e6 - lon) * kx, ey = (this.lat[i] / 1e6 - lat) * ky;
            const d = ex * ex + ey * ey, s = this.kind[i] === this.J ? 0 : 1;
            if (d < bestD[s]) { bestD[s] = d; best[s] = i; }
          }
        }
      }
      return best[0] >= 0 ? best[0] : best[1];
    }
    /* builds the word index; a generator so the page can yield between chunks */
    *build() {
      const n = this.n, nn = new Array(n), map = new Map();
      const add = (w, i) => {
        let a = map.get(w);
        if (!a) map.set(w, a = []);
        if (a[a.length - 1] !== i) a.push(i);
      };
      for (let i = 0; i < n; i++) {
        const s = norm(this.name[i]);
        nn[i] = s;
        if (s) {
          for (const w of s.split(" ")) {
            add(w, i);
            const ex = EXPAND[w];
            if (ex) for (const e of ex) add(e, i);
          }
        }
        const l = this.loc[i];
        if (l >= 0 && this.locNorm[l]) for (const w of this.locNorm[l].split(" ")) add(w, i);
        if ((i & 8191) === 8191) yield i / n;
      }
      const toks = [...map.keys()].sort();
      const off = new Int32Array(toks.length + 1);
      let total = 0;
      for (let k = 0; k < toks.length; k++) { off[k] = total; total += map.get(toks[k]).length; }
      off[toks.length] = total;
      yield 0.95;
      const post = new Int32Array(total);
      for (let k = 0; k < toks.length; k++) post.set(map.get(toks[k]), off[k]);
      this.nn = nn; this.toks = toks; this.off = off; this.post = post;
      this.stamp = new Uint32Array(n); this.gen = 0;
      this.ready = true;
    }
    buildNow() { for (const _ of this.build()) { /* run to completion */ } return this; }

    /* [lo, hi) of the words starting with t */
    range(t) {
      const toks = this.toks;
      let lo = 0, hi = toks.length;
      while (lo < hi) { const m = (lo + hi) >> 1; if (toks[m] < t) lo = m + 1; else hi = m; }
      const a = lo;
      hi = toks.length;
      while (lo < hi) { const m = (lo + hi) >> 1; if (toks[m].startsWith(t) || toks[m] < t) lo = m + 1; else hi = m; }
      return { lo: a, hi: lo, count: this.off[lo] - this.off[a] };
    }
    halves(i) {
      let h = this._halves.get(i);
      if (!h) { h = this.name[i].split(/\s*&\s*/).map(norm); this._halves.set(i, h); }
      return h;
    }
    /* score of a junction against a two-part query, or -1:
     * each part must start one of the junction's streets, a different one each */
    junctionScore(i, parts) {
      const hv = this.halves(i);
      if (hv.length < 2) return -1;
      const l = this.loc[i], loc = l >= 0 ? this.locNorm[l] : "";
      const fits = (p, h) => {
        if (!p.toks.length || !wordPrefix(h, p.toks[0], p.partial && p.toks.length === 1)) return false;
        return p.toks.every((t, k) => wordPrefix(h + " " + loc, t, p.partial && k === p.toks.length - 1));
      };
      for (let a = 0; a < hv.length; a++) {
        if (!fits(parts[0], hv[a])) continue;
        for (let b = 0; b < hv.length; b++) {
          if (b === a || !fits(parts[1], hv[b])) continue;
          return (parts[0].qa === hv[a] && parts[1].qa === hv[b]) ? 0 : 1;
        }
      }
      return -1;
    }
    score(i, Q, parts) {
      const nn = this.nn[i];
      let s = -1;
      if (nn === Q.qa || nn === Q.q) s = 0;
      else if (nn.startsWith(Q.q) || startsWithWords(nn, Q.qa)) s = 1;
      else if (Q.partial) {
        const head = Q.toks.slice(0, -1).join(" "), last = Q.toks[Q.toks.length - 1];
        for (const a of abbrevsFor(last)) if (startsWithWords(nn, (head ? head + " " : "") + a)) { s = 1; break; }
      }
      if (s < 0) {
        const l = this.loc[i], hay = l >= 0 ? nn + " " + this.locNorm[l] : nn;
        let all = true;
        for (let k = 0; k < Q.toks.length; k++) {
          if (!wordPrefix(hay, Q.toks[k], Q.partial && k === Q.toks.length - 1)) { all = false; break; }
        }
        if (all) s = 2;
      }
      if (this.kind[i] === this.J) {
        if (parts.length === 2) {
          const js = this.junctionScore(i, parts);
          if (js >= 0) return [js, 0];
        }
        // a bare street name finds the street first, its junctions after
        return s < 0 ? null : [Math.max(s, 2), 1];
      }
      return s < 0 ? null : [s, 1];
    }

    search(raw, limit = 8, postcodes = null) {
      const out = [];
      if (postcodes) for (const r of postcodes.lookup(raw)) out.push(r);
      const lowered = String(raw).toLowerCase().replace(/^\s*(?:the\s+)?(?:corner|junction)\s+of\s+/, "");
      // "A & B", "A and B", "A at B", "A / B": the first part is complete, the last may be half typed
      const raws = lowered.split(/\s+(?:and|at)\s+|\s*[&\/@+]\s*/).filter((p) => p.trim());
      const parts = raws.map((p, k) => parseQuery(k < raws.length - 1 ? p + " " : p));
      // the words of every part, without the "and" / "at" between them
      const Q = parseQuery(raws.length === 2 ? raws.join(" ") : lowered);
      if (Q.toks.length && this.ready) {
        // drive the scan from the rarest query word
        let best = null;
        for (const t of Q.toks) {
          const r = this.range(t);
          if (!best || r.count < best.count) best = r;
        }
        const cap = 60000, gen = ++this.gen;
        let seen = 0;
        for (let p = this.off[best.lo], e = this.off[best.hi]; p < e && seen < cap; p++) {
          const i = this.post[p];
          if (this.stamp[i] === gen) continue;
          this.stamp[i] = gen; seen++;
          const sc = this.score(i, Q, parts);
          if (!sc) continue;
          out.push({ score: sc[0], tier: sc[1], rank: this.rank[i] || 0, i,
            name: this.display(i), kind: this.kinds[this.kind[i]],
            lon: this.lon[i] / 1e6, lat: this.lat[i] / 1e6 });
        }
      }
      out.sort((a, b) => a.score - b.score || a.tier - b.tier || b.rank - a.rank || a.name.length - b.name.length
        || (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
      const seenK = new Set(), res = [];
      for (const r of out) {
        const k = r.kind + "|" + r.name;
        if (seenK.has(k)) continue;
        seenK.add(k); res.push(r);
        if (res.length >= limit) break;
      }
      return res;
    }
  }

  /* ------------------------------------------------------------ postcodes */
  /* postcodes.bin (design 3.4): "FLPC", n, J, J bytes of {"out": [...]},
   * padding to 4, then n records of (u16 outward index, u16 inward code,
   * i32 lon, i32 lat), sorted by outward then inward. */
  const PC_LETTERS = "ABDEFGHJLNPQRSTUWXYZ";
  const OUT_RE = /^[A-Z]{1,2}\d[A-Z\d]?$/;
  const looksLikePostcode = (raw) => /^\s*[A-Za-z]{1,2}\d/.test(raw);
  function inwardRange(part) {
    // "1" -> all of sector 1; "1A" -> 1A?; "1AA" -> that unit
    const d = +part[0];
    if (part.length === 1) return [d * 400, d * 400 + 399];
    const a = PC_LETTERS.indexOf(part[1]);
    if (a < 0) return null;
    if (part.length === 2) return [d * 400 + a * 20, d * 400 + a * 20 + 19];
    const b = PC_LETTERS.indexOf(part[2]);
    if (b < 0) return null;
    return [d * 400 + a * 20 + b, d * 400 + a * 20 + b];
  }
  class Postcodes {
    constructor(buf) {
      const u8 = buf instanceof Uint8Array ? buf : new Uint8Array(buf);
      const dv = new DataView(u8.buffer, u8.byteOffset, u8.byteLength);
      if (String.fromCharCode(u8[0], u8[1], u8[2], u8[3]) !== "FLPC") throw new Error("not a postcode file");
      this.n = dv.getUint32(4, true);
      const J = dv.getUint32(8, true);
      this.out = JSON.parse(new TextDecoder().decode(u8.subarray(12, 12 + J))).out;
      this.outIdx = new Map(this.out.map((o, i) => [o, i]));
      let start = 12 + J;
      start += (4 - (start % 4)) % 4;
      this.dv = new DataView(u8.buffer, u8.byteOffset + start, this.n * 12);
      this._centroid = new Map();
    }
    outOf(i) { return this.dv.getUint16(i * 12, true); }
    inOf(i) { return this.dv.getUint16(i * 12 + 2, true); }
    lonOf(i) { return this.dv.getInt32(i * 12 + 4, true) / 1e6; }
    latOf(i) { return this.dv.getInt32(i * 12 + 8, true) / 1e6; }
    /* first record with key >= (o, inward) */
    lower(o, inward) {
      let lo = 0, hi = this.n;
      while (lo < hi) {
        const m = (lo + hi) >> 1, mo = this.outOf(m);
        if (mo < o || (mo === o && this.inOf(m) < inward)) lo = m + 1; else hi = m;
      }
      return lo;
    }
    unitName(i) {
      const c = this.inOf(i);
      return this.out[this.outOf(i)] + " " + Math.floor(c / 400) + PC_LETTERS[Math.floor(c % 400 / 20)] + PC_LETTERS[c % 20];
    }
    units(outward, part, limit) {
      const o = this.outIdx.get(outward);
      if (o === undefined) return [];
      const r = inwardRange(part);
      if (!r) return [];
      const res = [];
      for (let i = this.lower(o, r[0]); i < this.n && res.length < limit; i++) {
        if (this.outOf(i) !== o || this.inOf(i) > r[1]) break;
        res.push(i);
      }
      return res;
    }
    centroid(outward) {
      let c = this._centroid.get(outward);
      if (c) return c;
      const o = this.outIdx.get(outward);
      if (o === undefined) return null;
      let x = 0, y = 0, k = 0;
      for (let i = this.lower(o, 0); i < this.n && this.outOf(i) === o; i++) { x += this.lonOf(i); y += this.latOf(i); k++; }
      c = k ? { lon: x / k, lat: y / k, n: k } : null;
      this._centroid.set(outward, c);
      return c;
    }
    /* search results for a postcode-shaped query: exact unit, district, or units by prefix */
    lookup(raw, limit = 8) {
      const s = String(raw).trim().toUpperCase().replace(/\s+/g, " ");
      const res = [];
      const unit = (i, score) => ({ score, tier: 0, rank: 255, name: this.unitName(i),
        kind: "postcode", lon: this.lonOf(i), lat: this.latOf(i) });
      let m;
      if (s.includes(" ")) {
        m = /^([A-Z]{1,2}\d[A-Z\d]?) (\d[A-Z]{0,2})$/.exec(s);
        if (!m) return res;
        for (const i of this.units(m[1], m[2], limit)) res.push(unit(i, m[2].length === 3 ? -1 : 1));
        return res;
      }
      m = /^([A-Z]{1,2}\d[A-Z\d]?)(\d[A-Z]{2})$/.exec(s);
      if (m) for (const i of this.units(m[1], m[2], 1)) res.push(unit(i, -1));
      if (OUT_RE.test(s)) {
        const c = this.centroid(s);
        if (c) res.push({ score: 0.5, tier: 0, rank: 255, name: s, kind: "postcode district", lon: c.lon, lat: c.lat });
        // "E11" is also E1 plus sector 1: offer a couple of those units too, capped
        for (let k = 2; k < s.length; k++) {
          const o = s.slice(0, k), rest = s.slice(k);
          if (!OUT_RE.test(o) || !/^\d[A-Z]?$/.test(rest)) continue;
          for (const i of this.units(o, rest, 2)) res.push(unit(i, 1));
        }
        return res.slice(0, 3);
      }
      if (!res.length) {
        for (let k = 2; k < s.length; k++) {
          const o = s.slice(0, k), rest = s.slice(k);
          if (!OUT_RE.test(o) || !/^\d[A-Z]?$/.test(rest)) continue;
          for (const i of this.units(o, rest, limit - res.length)) res.push(unit(i, 1));
        }
      }
      return res;
    }
  }

  /* ---------------------------------------------------------- share links */
  /* The trip travels in the URL fragment as one bare token of letters,
   * digits and . _ ~ - (labels hex-escaped), which survives any host, link
   * shortener or chat client that mangles key=value fragments. SF grammar:
   * #t~fromLon~fromLat~toLon~toLat~w|b~t~fromLabel~toLabel. Labels are
   * escaped per UTF-16 unit, so characters beyond U+FFFF survive as a
   * surrogate pair of _uXXXX escapes (SF wrote 5 hex digits it could not read back). */
  function encLabel(s) {
    s = String(s || "");
    let out = "";
    for (let k = 0; k < s.length; k++) {
      const ch = s[k], c = s.charCodeAt(k);
      if (/[A-Za-z0-9.\-]/.test(ch)) out += ch;
      else out += c < 256 ? "_" + c.toString(16).padStart(2, "0") : "_u" + c.toString(16).padStart(4, "0");
    }
    return out;
  }
  function decLabel(s) {
    return String(s || "").replace(/_u([0-9a-f]{4})|_([0-9a-f]{2})/gi, (m, u, b) => String.fromCharCode(parseInt(u || b, 16)));
  }
  function makeToken(st) {
    const c = (p) => p.lon.toFixed(5) + "~" + p.lat.toFixed(5);
    return ["t", c(st.from), c(st.to), st.mode === "bike" ? "b" : "w", st.t.toFixed(3),
      encLabel(st.from.label), encLabel(st.to.label)].join("~");
  }
  /* the part of a token that names the trip itself: both ends (place and name: a postcode
   * that snaps to the same junction as a station is still a new choice) and the mode, not
   * the slider */
  function tripKey(st) {
    const c = (p) => p.lon.toFixed(5) + "~" + p.lat.toFixed(5) + "~" + encLabel(p.label);
    return [c(st.from), c(st.to), st.mode === "bike" ? "b" : "w"].join("~");
  }
  function parseToken(h) {
    if (!h || h.length < 2) return null;
    const parts = h.replace(/^#/, "").split("~");
    if (parts[0] !== "t" || parts.length < 8) return null;
    const nums = parts.slice(1, 5).map(Number);
    if (nums.some((v) => !Number.isFinite(v))) return null;
    const tt = parseFloat(parts[6]);
    return { from: { lon: nums[0], lat: nums[1], label: decLabel(parts[7]) },
      to: { lon: nums[2], lat: nums[3], label: decLabel(parts[8] || "") },
      mode: parts[5] === "b" ? "bike" : "walk", t: Number.isFinite(tt) ? clamp(tt, 0, 1) : null };
  }

  /* ---------------------------------------------------------- geography */
  /* even-odd test over every ring of a GeoJSON (Multi)Polygon in lon/lat */
  function insidePolygon(geom, lon, lat) {
    const polys = geom.type === "Polygon" ? [geom.coordinates] : geom.coordinates;
    let inside = false;
    for (const poly of polys) {
      for (const ring of poly) {
        for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
          const [x1, y1] = ring[i], [x2, y2] = ring[j];
          if ((y1 > lat) !== (y2 > lat) && lon < (x2 - x1) * (lat - y1) / (y2 - y1) + x1) inside = !inside;
        }
      }
    }
    return inside;
  }
  /* metres from (lon, lat) to the nearest boundary edge (local equirectangular) */
  function distToBoundary(geom, lon, lat) {
    const polys = geom.type === "Polygon" ? [geom.coordinates] : geom.coordinates;
    const kx = 111320 * Math.cos(lat * Math.PI / 180), ky = 110540;
    let best = Infinity;
    for (const poly of polys) {
      for (const ring of poly) {
        for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
          const ax = (ring[j][0] - lon) * kx, ay = (ring[j][1] - lat) * ky;
          const bx = (ring[i][0] - lon) * kx, by = (ring[i][1] - lat) * ky;
          const dx = bx - ax, dy = by - ay, L = dx * dx + dy * dy;
          const t = L ? clamp(-(ax * dx + ay * dy) / L, 0, 1) : 0;
          const d = Math.hypot(ax + t * dx, ay + t * dy);
          if (d < best) best = d;
        }
      }
    }
    return best;
  }
  /* [[south, west], [north, east]] of a GeoJSON (Multi)Polygon */
  function geomBounds(geom) {
    const polys = geom.type === "Polygon" ? [geom.coordinates] : geom.coordinates;
    let w = Infinity, s = Infinity, e = -Infinity, n = -Infinity;
    for (const poly of polys) for (const ring of poly) for (const [x, y] of ring) {
      if (x < w) w = x; if (x > e) e = x; if (y < s) s = y; if (y > n) n = y;
    }
    return [[s, w], [n, e]];
  }
  /* within Greater London, or less than slackM outside it */
  function inLondon(geom, lon, lat, slackM = 250) {
    if (!geom) return true;
    return insidePolygon(geom, lon, lat) || distToBoundary(geom, lon, lat) <= slackM;
  }
  /* Web Mercator at zoom 0 (a 256 px world), as Leaflet's EPSG:3857 */
  const mercX = (lon) => (lon + 180) / 360 * 256;
  const mercY = (lat) => {
    const s = Math.sin(clamp(lat, -85.0511, 85.0511) * Math.PI / 180);
    return (0.5 - Math.log((1 + s) / (1 - s)) / (4 * Math.PI)) * 256;
  };

  /* ---------------------------------------------------------- tile files */
  /* GitHub Pages serves .gz as application/gzip without Content-Encoding,
   * so the bytes usually arrive compressed; the gzip magic tells. */
  async function inflateBytes(bytes) {
    if (!(bytes.length > 2 && bytes[0] === 0x1f && bytes[1] === 0x8b)) return bytes;
    if (typeof DecompressionStream === "undefined") {
      throw new Error("this browser has no DecompressionStream; please use a "
        + "current version of Chrome, Firefox, Edge or Safari");
    }
    const stream = new Blob([bytes]).stream().pipeThrough(new DecompressionStream("gzip"));
    return new Uint8Array(await new Response(stream).arrayBuffer());
  }
  const TYPES = { i1: Int8Array, u1: Uint8Array, i2: Int16Array, u2: Uint16Array,
    i4: Int32Array, u4: Uint32Array, f4: Float32Array, f8: Float64Array };
  /* FLT1 (design 4.3): magic, u32 header length, JSON header, 8-byte aligned arrays */
  function parseFLT1(u8) {
    if (String.fromCharCode(u8[0], u8[1], u8[2], u8[3]) !== "FLT1") throw new Error("not an FLT1 tile");
    const dv = new DataView(u8.buffer, u8.byteOffset, u8.byteLength);
    const H = dv.getUint32(4, true);
    const head = JSON.parse(new TextDecoder().decode(u8.subarray(8, 8 + H)));
    const arrays = {}, strings = {};
    for (const [name, m] of Object.entries(head.arrays || {})) {
      const T = TYPES[m.t];
      const o = u8.byteOffset + m.o;
      arrays[name] = o % T.BYTES_PER_ELEMENT === 0 ? new T(u8.buffer, o, m.n)
        : new T(u8.slice(m.o, m.o + m.n * T.BYTES_PER_ELEMENT).buffer, 0, m.n);
    }
    for (const [name, m] of Object.entries(head.strings || {})) strings[name] = { o: m.o, b: m.b };
    return { u8, arrays, strings };
  }
  /* Decode a tile's edge polylines (precision 5, lat/lon, per edge) straight
   * into Mercator z0 coordinates relative to the tile's first point, plus a
   * per-edge bbox; no intermediate JS arrays. */
  function decodeTileGeometry(tile) {
    const s = tile.strings.geom, u8 = tile.u8, off = tile.arrays.geom_off;
    const base = s.o, end = s.o + s.b, ne = off.length - 1;
    let nv = 0;
    for (let i = base; i < end; i++) if (u8[i] < 95) nv++;
    const xy = new Float32Array(nv), starts = new Int32Array(ne + 1), bbox = new Float32Array(ne * 4);
    let k = 0, ox = NaN, oy = NaN;
    for (let e = 0; e < ne; e++) {
      starts[e] = k;
      let i = base + off[e];
      const stop = base + off[e + 1];
      let lat = 0, lon = 0, x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
      while (i < stop) {
        let b, shift = 0, result = 0;
        do { b = u8[i++] - 63; result |= (b & 0x1f) << shift; shift += 5; } while (b >= 0x20);
        lat += (result & 1) ? ~(result >> 1) : (result >> 1);
        shift = 0; result = 0;
        do { b = u8[i++] - 63; result |= (b & 0x1f) << shift; shift += 5; } while (b >= 0x20);
        lon += (result & 1) ? ~(result >> 1) : (result >> 1);
        const X = mercX(lon / 1e5), Y = mercY(lat / 1e5);
        if (ox !== ox) { ox = X; oy = Y; }
        const x = X - ox, y = Y - oy;
        xy[k++] = x; xy[k++] = y;
        if (x < x0) x0 = x; if (x > x1) x1 = x; if (y < y0) y0 = y; if (y > y1) y1 = y;
      }
      bbox[e * 4] = x0; bbox[e * 4 + 1] = y0; bbox[e * 4 + 2] = x1; bbox[e * 4 + 3] = y1;
    }
    starts[ne] = k;
    return { xy: xy.subarray(0, k), starts, bbox, ox: ox !== ox ? 0 : ox, oy: oy !== oy ? 0 : oy,
      len: tile.arrays.edge_len, n: ne };
  }

  /* ---------------------------------------------------------- route bits */
  const STREET_SHORT = { Street: "St", Road: "Rd", Avenue: "Ave", Gardens: "Gdns", Crescent: "Cres",
    Square: "Sq", Place: "Pl", Terrace: "Ter", Lane: "Ln", Drive: "Dr", Court: "Ct", Grove: "Gr",
    Close: "Cl", Boulevard: "Blvd", Highway: "Hwy", Parkway: "Pkwy" };
  function shortStreet(name) {
    return String(name).split(" ").map((w) => STREET_SHORT[w] || w).join(" ");
  }
  /* named runs of at least minRun metres, re-merged across what was dropped
   * ("Kentish Town Rd, Kentish Town Rd" either side of a nameless crossing) */
  function namedRuns(runs, minRun) {
    const out = [];
    for (const r of runs || []) {
      if (!r.name || !(r.length_m >= minRun)) continue;
      const last = out[out.length - 1];
      if (last && last.name === r.name) { last.length_m += r.length_m; continue; }
      out.push({ name: r.name, length_m: r.length_m, mid: r.mid, bearing: r.bearing });
    }
    return out;
  }
  const Core = { MI, FT, KM, clamp, lerp, ease, hexToRgb, rampOf, makeUnits, fmtPct, ABBREV, EXPAND,
    abbrevsFor, words, norm, parseQuery, wordPrefix, SearchIndex, Postcodes, looksLikePostcode,
    encLabel, decLabel, makeToken, parseToken, insidePolygon, distToBoundary, geomBounds, inLondon, mercX, mercY,
    inflateBytes, parseFLT1, decodeTileGeometry, shortStreet, namedRuns };
  if (typeof module === "object" && module.exports) module.exports = Core;
  if (typeof document === "undefined" || !root.FLR) return;
  root.FLRCore = Core;

  /* ================================================================ app */
  const $ = (id) => document.getElementById(id);
  const css = (name) => getComputedStyle(document.documentElement).getPropertyValue(name).trim();
  const ramp = (t) => rampOf([css("--short"), css("--mid"), css("--route")], t);
  const store = {
    get(k) { try { return localStorage.getItem(k); } catch (e) { return null; } },
    set(k, v) { try { localStorage.setItem(k, v); } catch (e) { /* private mode */ } },
  };
  const UNITS_KEY = "flattenlondon.units";
  const statusEl = () => $("status");
  function setStatus(text, warn) {
    const el = statusEl();
    el.textContent = text;
    el.classList.toggle("warn", !!warn);
  }
  class NotFound extends Error {}

  /* --------------------------------------------- vector street canvas */
  /* SF drew every edge of its one graph on each redraw. Here the streets
   * come from the graph tiles in view, fetched (the HTTP cache shares them
   * with the worker), decoded once into Mercator coordinates and cached.
   * Below the basemap's streets_maxzoom the raster already has streets. */
  const StreetLayer = L.Layer.extend({
    initialize(app) { this.app = app; this.cache = new Map(); this.loading = new Set(); this.queue = []; },
    onAdd(map) {
      this._map = map;
      this._canvas = L.DomUtil.create("canvas", "leaflet-zoom-animated streets");
      map.getPanes().overlayPane.appendChild(this._canvas);
      map.on("moveend zoomend resize", this._update, this);
      map.on("zoomanim", this._animate, this);
      this._update();
    },
    onRemove(map) {
      L.DomUtil.remove(this._canvas);
      map.off("moveend zoomend resize", this._update, this);
      map.off("zoomanim", this._animate, this);
    },
    reset() { this.cache.clear(); this.queue = []; this._update(); },
    _animate(e) {
      const scale = this._map.getZoomScale(e.zoom);
      const offset = this._map._latLngToNewLayerPoint(this._map.getBounds().getNorthWest(), e.zoom, e.center);
      L.DomUtil.setTransform(this._canvas, offset, scale);
    },
    active() {
      const bm = this.app.index.basemap;
      return Math.round(this._map.getZoom()) > (bm ? bm.streets_maxzoom : 13);
    },
    visible() {
      const b = this._map.getBounds().pad(0.05);
      const w = b.getWest(), e = b.getEast(), s = b.getSouth(), n = b.getNorth();
      return this.app.index.tiles.filter((t) => !(t.bbox[2] < w || t.bbox[0] > e || t.bbox[3] < s || t.bbox[1] > n));
    },
    _update() {
      this._redraw();
      if (!this.active()) return;
      for (const t of this.visible()) {
        const key = t.url;
        if (this.cache.has(key) || this.loading.has(key)) continue;
        this.loading.add(key);
        this.app.fetchBytes(() => t.url)
          .then((u8) => {
            this.cache.set(key, decodeTileGeometry(parseFLT1(u8)));
            // keep the most recent tiles only
            if (this.cache.size > 48) this.cache.delete(this.cache.keys().next().value);
          })
          .catch((err) => console.warn("street tile", t.url, err))
          .finally(() => { this.loading.delete(key); this._soon(); });
      }
    },
    _soon() {
      if (this._raf) return;
      this._raf = requestAnimationFrame(() => { this._raf = 0; this._redraw(); });
    },
    _redraw() {
      const map = this._map; if (!map) return;
      const size = map.getSize(), dpr = window.devicePixelRatio || 1;
      if (this._canvas.width !== size.x * dpr || this._canvas.height !== size.y * dpr) {
        this._canvas.width = size.x * dpr; this._canvas.height = size.y * dpr;
        this._canvas.style.width = size.x + "px"; this._canvas.style.height = size.y + "px";
      }
      const nw = map.getBounds().getNorthWest();
      L.DomUtil.setTransform(this._canvas, map.latLngToLayerPoint(nw), 1);
      const ctx = this._canvas.getContext("2d");
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      ctx.clearRect(0, 0, size.x, size.y);
      if (!this.active()) return;
      const z = map.getZoom(), scale = Math.pow(2, z);
      const p0 = map.project(nw, z);
      const pad = 8 / scale;
      const vx0 = p0.x / scale - pad, vy0 = p0.y / scale - pad;
      const vx1 = (p0.x + size.x) / scale + pad, vy1 = (p0.y + size.y) / scale + pad;
      const minLen = (z >= 15 ? 0 : z >= 14 ? 10 : 20) * 20;  // edge_len is in 5 cm units
      ctx.strokeStyle = css("--street") || "#c9ccc9";
      ctx.lineWidth = z >= 16 ? 1.6 : z >= 15 ? 1.3 : 1.1;
      ctx.lineCap = "round"; ctx.lineJoin = "round";
      ctx.beginPath();
      for (const t of this.visible()) {
        const g = this.cache.get(t.url);
        if (!g) continue;
        const ax = g.ox * scale - p0.x, ay = g.oy * scale - p0.y;
        const bx0 = vx0 - g.ox, by0 = vy0 - g.oy, bx1 = vx1 - g.ox, by1 = vy1 - g.oy;
        const xy = g.xy, st = g.starts, bb = g.bbox, len = g.len;
        for (let e = 0; e < g.n; e++) {
          const o = e * 4;
          if (bb[o + 2] < bx0 || bb[o] > bx1 || bb[o + 3] < by0 || bb[o + 1] > by1) continue;
          if (minLen && len && len[e] < minLen) continue;
          const s = st[e], f = st[e + 1];
          if (f - s < 4) continue;
          ctx.moveTo(ax + xy[s] * scale, ay + xy[s + 1] * scale);
          for (let k = s + 2; k < f; k += 2) ctx.lineTo(ax + xy[k] * scale, ay + xy[k + 1] * scale);
        }
      }
      ctx.stroke();
    },
  });

  /* -------------------------------------------------------- map labels */
  /* Boroughs far out, areas in the middle, parks and water close in, each
   * with its zoom range; placed greedily by rank so none overlap each other,
   * the highlighted route, or what floats over the map (the card, controls). */
  const LabelLayer = L.Layer.extend({
    initialize(labels, obstacles) { this.labels = labels || []; this.avoid = []; this.obstacles = obstacles; },
    onAdd(map) {
      this._map = map;
      this._group = L.layerGroup().addTo(map);
      map.on("moveend zoomend resize", this._update, this);
      this._update();
    },
    onRemove(map) { map.removeLayer(this._group); map.off("moveend zoomend resize", this._update, this); },
    setLabels(labels) { this.labels = labels || []; this._update(); },
    setAvoid(lines) { this.avoid = lines || []; if (this._map) this._update(); },
    /* the cells (6 px) the lines to avoid pass through, in container pixels */
    _occupied(map, size) {
      const C = 6, cols = Math.ceil(size.x / C) + 2, rows = Math.ceil(size.y / C) + 2;
      const grid = new Uint8Array(cols * rows);
      const mark = (x, y) => {
        const cx = Math.floor(x / C) + 1, cy = Math.floor(y / C) + 1;
        if (cx >= 0 && cy >= 0 && cx < cols && cy < rows) grid[cy * cols + cx] = 1;
      };
      for (const line of this.avoid) {
        let prev = null;
        for (const ll of line) {
          const p = map.latLngToContainerPoint(ll);
          if (prev && !((p.x < 0 && prev.x < 0) || (p.y < 0 && prev.y < 0)
            || (p.x > size.x && prev.x > size.x) || (p.y > size.y && prev.y > size.y))) {
            const dx = p.x - prev.x, dy = p.y - prev.y, n = Math.ceil(Math.hypot(dx, dy) / 3) || 1;
            for (let k = 0; k <= n; k++) mark(prev.x + dx * k / n, prev.y + dy * k / n);
          }
          prev = p;
        }
      }
      return { grid, cols, rows, C,
        hit(b) {
          const x0 = Math.max(0, Math.floor(b[0] / C) + 1), x1 = Math.min(cols - 1, Math.floor(b[2] / C) + 1);
          const y0 = Math.max(0, Math.floor(b[1] / C) + 1), y1 = Math.min(rows - 1, Math.floor(b[3] / C) + 1);
          for (let y = y0; y <= y1; y++) for (let x = x0; x <= x1; x++) if (grid[y * cols + x]) return true;
          return false;
        } };
    },
    _update() {
      const map = this._map, z = map.getZoom(), size = map.getSize();
      this._group.clearLayers();
      const occ = this.avoid.length ? this._occupied(map, size) : null;
      const obs = this.obstacles ? this.obstacles() : [];
      const cands = [];
      for (const l of this.labels) {
        if (z < (l.z0 == null ? 0 : l.z0) || z >= (l.z1 == null ? 99 : l.z1)) continue;
        const p = map.latLngToContainerPoint([l.lat, l.lon]);
        if (p.x < -100 || p.y < -20 || p.x > size.x + 100 || p.y > size.y + 20) continue;
        cands.push([l, p]);
      }
      cands.sort((a, b) => (b[0].r || 0) - (a[0].r || 0));
      const boxes = [];
      for (const [l, p] of cands) {
        if (boxes.length >= 80) break;
        const wide = l.k === "borough" ? 8.4 : 6.4;
        const w = String(l.n).length * wide + 10, h = 16;
        const box = [p.x - w / 2, p.y - h / 2, p.x + w / 2, p.y + h / 2];
        if (box[0] < 2 || box[1] < 2 || box[2] > size.x - 2 || box[3] > size.y - 2) continue;  // no half labels
        const meets = (b) => box[0] < b[2] && box[2] > b[0] && box[1] < b[3] && box[3] > b[1];
        if (boxes.some(meets) || obs.some(meets)) continue;
        if (occ && occ.hit(box)) continue;
        boxes.push(box);
        const m = L.marker([l.lat, l.lon], { interactive: false, keyboard: false,
          icon: L.divIcon({ className: "maplabel k-" + (l.k || "area"), html: "<span></span>", iconSize: null }) });
        m.addTo(this._group);
        m.getElement().firstChild.textContent = l.n;
      }
    },
  });

  /* -------------------------------------------------------------- the app */
  const App = {
    state: { mode: "walk", from: null, to: null, t: 1, focus: "from" },
    family: null, shown: null, _gen: 0, _snapId: 0, _seq: { from: 0, to: 0 },
    units: makeUnits(store.get(UNITS_KEY) === "imperial" ? "imperial" : "metric"),
    ALPHA_MAX: 200,

    async start() {
      this.indexUrl = root.FLR.index_url;
      this.workerUrl = root.FLR.worker_url;
      this._pending = new Map();
      setStatus("Loading London…");
      this.index = await this.loadIndex(this.indexUrl);
      this.ALPHA_MAX = this.index.meta.alpha_max || 200;
      this.buildMap();
      this.buildUI();
      this.startWorker();
      await this.ready;
      setStatus("");
      const restored = await this.readHash();
      if (!restored && this.index.default && this.index.default.length === 2) {
        const [a, b] = await Promise.all(this.index.default.map((p) => this.pointAt(p.lon, p.lat, p.label)));
        if (!a.error) this.setPoint("from", a, false);
        if (!b.error) this.setPoint("to", b, false);
      }
      this.recompute(true);
    },

    /* --------------------------------------------------- data and recovery */
    async loadIndex(url) {
      const res = await fetch(url);
      if (res.status === 404 && !this._retriedIndex) {
        this._retriedIndex = true;
        const cur = await this.current();
        if (cur && cur.index_url && cur.index_url !== url) {
          this.indexUrl = cur.index_url;
          if (cur.worker_url) this.workerUrl = cur.worker_url;
          return this.loadIndex(cur.index_url);
        }
      }
      if (!res.ok) throw new Error("could not load " + url + " (" + res.status + ")");
      return res.json();
    },
    async current() {
      try {
        const r = await fetch("current.json", { cache: "no-store" });
        return r.ok ? await r.json() : null;
      } catch (e) { return null; }
    },
    /* A hashed file 404s when a deploy lands mid-session: fetch current.json
     * with no-store, and if it names a new index, reload the index, restart
     * the worker and re-snap the trip on the new graph. True if it did. */
    recover() {
      if (this._recovering) return this._recovering;
      this._recovering = (async () => {
        const cur = await this.current();
        if (!cur || !cur.index_url || cur.index_url === this.indexUrl) return false;
        const index = await this.loadIndex(cur.index_url);
        this.indexUrl = cur.index_url;
        if (cur.worker_url) this.workerUrl = cur.worker_url;
        this.index = index;
        this._placesP = null; this._searchP = null; this._postcodesP = null;
        this.places = null; this.postcodes = null;
        this.basemap.setUrl(this.basemapUrl());
        this.mapLabels.setLabels(index.labels);
        this.streets.reset();
        this.startWorker();
        await this.ready;
        // node ids belong to the old graph: snap the endpoints again (not via pointAt, which may wait on this)
        for (const w of ["from", "to"]) {
          const p = this.state[w];
          if (!p) continue;
          const r = await this.snap(p.lon, p.lat);
          this.state[w] = r.error ? null : Object.assign({}, p, { node: r.node, lon: r.lon, lat: r.lat });
        }
        this.drawMarkers();
        // the old worker took any route in flight with it: ask the new one
        if (this._routing) this.recompute(this._fit === true ? "auto" : this._fit);
        return true;
      })().finally(() => { this._recovering = null; });
      return this._recovering;
    },
    /* bytes of a hashed data file (gunzipped); getUrl is re-read after a recovery */
    async fetchBytes(getUrl, onProgress) {
      for (let attempt = 0; attempt < 2; attempt++) {
        const url = getUrl();
        const res = await fetch(url);
        if (res.status === 404 && attempt === 0 && await this.recover()) continue;
        if (!res.ok) throw new Error("could not load " + url + " (" + res.status + ")");
        return inflateBytes(new Uint8Array(await res.arrayBuffer()));
      }
      throw new NotFound("gone");
    },

    /* -------------------------------------------------------------- worker */
    startWorker() {
      if (this.worker) this.worker.terminate();
      for (const p of this._pending.values()) p({ error: "restart" });
      this._pending.clear();
      const w = new Worker(this.workerUrl);
      this.worker = w;
      this.ready = new Promise((res, rej) => { this._readyRes = res; this._readyRej = rej; });
      this.ready.catch(() => {});
      w.onmessage = (e) => this.onWorker(e.data);
      w.onerror = (e) => {
        console.error("worker", e);
        setStatus("Could not start the route finder: " + (e.message || "worker error"), true);
        this._readyRej(new Error(e.message || "worker error"));
      };
      w.postMessage({ type: "init", index_url: new URL(this.indexUrl, location.href).href });
    },
    onWorker(m) {
      switch (m.type) {
        case "ready":
          this.meta = m.meta; this.release = m.release;
          this._readyRes();
          return;
        case "snapped": {
          const p = this._pending.get(m.id);
          if (p) { this._pending.delete(m.id); p(m); }
          return;
        }
        case "progress":
          if (m.gen !== this._gen) return;
          this.onProgress(m);
          return;
        case "family":
          if (m.gen !== this._gen) return;
          this.onFamily(m);
          return;
        case "error":
          if (m.init || m.gen === -1) {  // init failed: the index did not load
            console.error("worker init", m);
            this._readyRej(new Error(m.message || m.code));
            return;
          }
          if (m.gen !== undefined && m.gen !== this._gen) return;
          this.onRouteError(m);
          return;
        default:
      }
    },
    snap(lon, lat) {
      const id = ++this._snapId;
      return new Promise((res) => {
        this._pending.set(id, res);
        this.worker.postMessage({ type: "snap", id, lon, lat, mode: this.state.mode });
      });
    },

    /* --------------------------------------------------------------- map */
    basemapUrl() {
      const bm = this.index.basemap;
      return bm.url + (bm.url.includes("?") ? "&" : "?") + "v=" + bm.v;
    },
    attribution(compact) {
      const y = String((this.index.release && this.index.release.built_at) || new Date().getFullYear()).slice(0, 4);
      const osm = "<a href='https://www.openstreetmap.org/copyright'>OpenStreetMap</a>";
      const ov = "<a href='https://overturemaps.org'>Overture</a>";
      if (compact) return "© " + osm + " contributors, " + ov + " · © Environment Agency · © OS, Royal Mail, ONS " + y;
      return "Streets © " + ov + " / " + osm + " contributors (ODbL) · Elevation © Environment Agency (OGL v3)"
        + " · Contains OS data © Crown copyright and database right " + y
        + " · Contains Royal Mail data © Royal Mail copyright and database right " + y
        + " · Contains National Statistics data © Crown copyright and database right " + y;
    },
    buildMap() {
      const bm = this.index.basemap;
      const bounds = L.latLngBounds(bm.bounds);
      // London's bbox is big enough to lose the city in: keep the view near it
      const london = L.latLngBounds(this.index.boundary ? geomBounds(this.index.boundary) : bm.bounds);
      const narrow = window.innerWidth <= 640;
      const map = L.map("map", {
        zoomControl: false, attributionControl: true, preferCanvas: true,
        center: [51.5074, -0.1278], zoom: narrow ? 9.5 : 10.5, minZoom: 9, maxZoom: 18, zoomSnap: 0.5,
        maxBounds: london.pad(0.6), maxBoundsViscosity: 0.8,
      });
      map.attributionControl.setPrefix("");
      this.map = map;
      this._attrCompact = null;
      this.layoutAttribution();
      $("attr_inline").innerHTML = this.attribution(false);
      L.control.zoom({ position: "bottomright" }).addTo(map);

      this.basemap = L.tileLayer(this.basemapUrl(), {
        minZoom: 9, maxZoom: 18, minNativeZoom: bm.minzoom, maxNativeZoom: bm.maxzoom,
        bounds, className: "basemap", keepBuffer: 2,
      }).addTo(map);
      this.streets = new StreetLayer(this).addTo(map);
      this.mapLabels = new LabelLayer(this.index.labels, () => this.obstacles()).addTo(map);

      const zoomClass = () => {
        const z = map.getZoom();
        map.getContainer().classList.toggle("z-low", z < 12);
        map.getContainer().classList.toggle("z-high", z >= 15.5);
        // past the basemap's own zooms its tiles are stretched and the terrain model's building
        // bumps grow into blobs: fade it under the vector streets
        map.getContainer().classList.toggle("z-over", z > bm.maxzoom + 0.5);
      };
      map.on("zoomend", zoomClass); zoomClass();
      // what fits on screen changes with zoom and position: relay the street names out
      map.on("moveend", () => { if (this._labelled) this.labelRoute(this._labelled); });

      this.familyLayer = L.layerGroup().addTo(map);
      this.routeLayer = L.layerGroup().addTo(map);
      this.markers = L.layerGroup().addTo(map);
      this.labelLayer = L.layerGroup().addTo(map);

      // the user taking the map: a route that arrives later is not fitted over their view
      const took = () => { this._moved = true; };
      for (const ev of ["pointerdown", "wheel", "keydown"]) map.getContainer().addEventListener(ev, took, { passive: true });

      // a double click zooms; only a single click sets an endpoint
      let timer = 0;
      map.on("click", (e) => {
        clearTimeout(timer);
        timer = setTimeout(() => this.onMapClick(e.latlng), 250);
      });
      map.on("dblclick", () => clearTimeout(timer));
    },
    layoutAttribution() {
      const compact = this.map.getSize().x <= 640;
      if (compact === this._attrCompact) return;
      const ac = this.map.attributionControl;
      if (this._attrText) ac.removeAttribution(this._attrText);
      this._attrText = this.attribution(compact);
      ac.addAttribution(this._attrText);
      ac.setPosition(compact ? "topright" : "bottomright");
      this._attrCompact = compact;
    },

    async onMapClick(ll) {
      const which = !this.state.from ? "from" : (!this.state.to ? "to" : this.state.focus);
      const seq = ++this._seq[which];
      const pt = await this.pointAt(ll.lng, ll.lat);
      if (seq !== this._seq[which]) return;
      if (pt.error) { this.pointError(pt.error); return; }
      this.setPoint(which, pt, true);
      this.recompute("auto");
    },
    pointError(code) {
      if (code === "restart") return;
      const msg = code === "outside" ? "That's outside Greater London."
        : code === "nonode" ? "No street near there." : "Could not reach the street network (" + code + ").";
      setStatus(msg, true);
      // the trip is unchanged: after a moment, say so again
      clearTimeout(this._statusTimer);
      this._statusTimer = setTimeout(() => {
        if (statusEl().textContent === msg && this.family && !this.family.partial) setStatus(this.familyStatus());
      }, 4000);
    },

    /* ---------------------------------------------------------- endpoints */
    /* A point is always a routable junction: whatever was clicked or
     * searched snaps (in the worker, for the current mode) to the nearest
     * one, so the pin sits where the route actually starts. Points outside
     * Greater London are refused. */
    async pointAt(lon, lat, label) {
      if (!inLondon(this.index.boundary, lon, lat)) return { error: "outside" };
      if (!label) this.ensurePlaces().catch(() => {});  // in parallel with the snap
      let r = await this.snap(lon, lat);
      // a tile 404s: a deploy landed mid-session
      if ((r.stale || r.error === "stale") && await this.recover()) r = await this.snap(lon, lat);
      if (r.error) return { error: r.error };
      return { lon: r.lon, lat: r.lat, node: r.node, label: label || ("near " + await this.describe(r.lon, r.lat)) };
    },
    /* "near Baker Street & Marylebone Road": the nearest junction in the place index */
    async describe(lon, lat) {
      let idx = null;
      try { idx = await this.ensurePlaces(); } catch (e) { console.warn(e); }
      const i = idx ? idx.nearest(lon, lat) : -1;
      if (i >= 0) return idx.name[i];
      return lat.toFixed(4) + ", " + lon.toFixed(4);
    },

    setPoint(which, pt, typed) {
      this.state[which] = pt;
      const input = $(which);
      input.value = pt ? pt.label : "";
      input.dataset.set = pt ? "1" : "";
      this.hideSuggest(which);
      this.drawMarkers();
      if (typed && !this.state[which === "from" ? "to" : "from"]) {
        $(which === "from" ? "to" : "from").focus();
      }
    },

    drawMarkers() {
      this.markers.clearLayers();
      for (const which of ["from", "to"]) {
        const p = this.state[which]; if (!p) continue;
        const m = L.marker([p.lat, p.lon], {
          draggable: true, keyboard: false, title: which === "from" ? "Start" : "Destination",
          icon: L.divIcon({ className: "pin-icon " + which, iconSize: [18, 18], iconAnchor: [9, 9] }),
        }).addTo(this.markers);
        // listening for click keeps a click on a pin from reaching the map
        m.on("click", () => {});
        m.on("dragend", async () => {
          const ll = m.getLatLng(), seq = ++this._seq[which];
          const pt = await this.pointAt(ll.lng, ll.lat);
          if (seq !== this._seq[which]) return;
          if (pt.error) { this.pointError(pt.error); this.drawMarkers(); return; }
          this.setPoint(which, pt, false);
          this.recompute(false);
        });
      }
    },

    /* ---------------------------------------------------- search, lazily */
    /* the place data alone (enough to name a dropped pin) */
    ensurePlaces() {
      if (!this._placesP) {
        this._placesP = (async () => {
          const bytes = await this.fetchBytes(() => this.index.search.url);
          const idx = new SearchIndex(JSON.parse(new TextDecoder().decode(bytes)));
          this.places = idx;
          return idx;
        })();
        this._placesP.catch(() => { this._placesP = null; });
      }
      return this._placesP;
    },
    /* ...and its word index, built in slices so typing stays smooth */
    ensureSearch() {
      if (!this._searchP) {
        this._searchP = (async () => {
          const idx = await this.ensurePlaces();
          if (idx.ready) return idx;
          let t0 = performance.now();
          for (const _ of idx.build()) {
            if (performance.now() - t0 > 12) {
              await new Promise((r) => setTimeout(r, 0));
              t0 = performance.now();
            }
          }
          return idx;
        })();
        this._searchP.catch((e) => { console.error(e); this._searchP = null; });
      }
      return this._searchP;
    },
    ensurePostcodes() {
      if (!this._postcodesP) {
        this._postcodesP = this.fetchBytes(() => this.index.postcodes.url).then((b) => (this.postcodes = new Postcodes(b)));
        this._postcodesP.catch((e) => { console.error(e); this._postcodesP = null; });
      }
      return this._postcodesP;
    },

    buildUI() {
      this.applyUnits();
      for (const which of ["from", "to"]) {
        const input = $(which), list = $(which + "_s");
        let sel = -1, items = [], note = "", timer = 0;
        const render = () => {
          list.innerHTML = "";
          items.forEach((it, i) => {
            const li = document.createElement("li");
            li.id = which + "_o" + i;
            li.setAttribute("role", "option");
            li.setAttribute("aria-selected", i === sel ? "true" : "false");
            li.innerHTML = "<span class='n'></span><span class='k'></span>";
            const comma = it.name.lastIndexOf(", ");
            if (it.kind !== "postcode" && comma > 0) {
              li.firstChild.textContent = it.name.slice(0, comma);
              const loc = document.createElement("span");
              loc.className = "loc"; loc.textContent = it.name.slice(comma);
              li.firstChild.appendChild(loc);
            } else li.firstChild.textContent = it.name;
            li.lastChild.textContent = it.kind;
            li.addEventListener("mousedown", (e) => { e.preventDefault(); pick(i); });
            list.appendChild(li);
          });
          if (note) {
            const li = document.createElement("li");
            li.className = "note"; li.textContent = note;
            list.appendChild(li);
          }
          list.hidden = items.length === 0 && !note;
          input.setAttribute("aria-expanded", list.hidden ? "false" : "true");
          if (sel >= 0 && items.length) {
            input.setAttribute("aria-activedescendant", which + "_o" + sel);
            const li = list.children[sel];
            if (li && li.scrollIntoView) li.scrollIntoView({ block: "nearest" });
          } else input.removeAttribute("aria-activedescendant");
        };
        const run = async () => {
          const q = input.value;
          if (!q.trim()) { items = []; note = ""; sel = -1; render(); return; }
          const pcWanted = looksLikePostcode(q);
          if (pcWanted && !this.postcodes) {
            this.ensurePostcodes().then(() => { if (input.value === q && document.activeElement === input) run(); }, () => {});
          }
          if (!this.places || !this.places.ready) {
            note = "Loading place search…"; items = this.postcodes && pcWanted ? this.postcodes.lookup(q) : [];
            sel = items.length ? 0 : -1; render();
            await this.ensureSearch().catch(() => {});
            if (input.value === q && document.activeElement === input) run();
            return;
          }
          items = this.places.search(q, 8, pcWanted ? this.postcodes : null);
          note = items.length ? "" : (pcWanted && !this.postcodes ? "Loading postcodes…" : "Nothing found offline. Try a postcode, station or two streets with &.");
          sel = items.length ? 0 : -1;
          render();
        };
        const pick = async (i) => {
          const it = items[i]; if (!it) return;
          items = []; note = ""; render();
          const seq = ++this._seq[which];
          input.value = it.name;
          const pt = await this.pointAt(it.lon, it.lat, it.name);
          if (seq !== this._seq[which]) return;
          if (pt.error) { this.pointError(pt.error); return; }
          this.setPoint(which, pt, true);
          this._refitAfterTyping = this.narrow();
          // on a phone the keyboard hides the result: put it away once both ends are set
          if (this.narrow() && this.state.from && this.state.to) input.blur();
          this.recompute("auto");
        };
        input.addEventListener("focus", () => {
          this.state.focus = which; $("card").classList.add("typing");
          if (input.dataset.set) input.select();
          this.ensureSearch().catch(() => {});
        });
        input.addEventListener("input", () => {
          input.dataset.set = "";
          clearTimeout(timer);
          timer = setTimeout(run, 60);
        });
        input.addEventListener("keydown", (e) => {
          if (e.key === "ArrowDown" && items.length) { sel = (sel + 1) % items.length; render(); e.preventDefault(); }
          else if (e.key === "ArrowUp" && items.length) { sel = (sel - 1 + items.length) % items.length; render(); e.preventDefault(); }
          else if (e.key === "Enter") {
            e.preventDefault();
            if (timer && input.value.trim()) { clearTimeout(timer); timer = 0; run().then(() => { if (sel >= 0) pick(sel); }); return; }
            if (sel >= 0) pick(sel);
          }
          else if (e.key === "Escape") { items = []; note = ""; render(); input.blur(); }
        });
        input.addEventListener("blur", () => {
          setTimeout(() => {
            // focused again meanwhile (Escape, then straight back in): the user is typing, keep it
            if (document.activeElement === input) return;
            items = []; note = ""; render();
            if (!input.dataset.set && this.state[which]) input.value = this.state[which].label;
            if (document.activeElement === $("from") || document.activeElement === $("to")) return;
            $("card").classList.remove("typing");
            // a pick while the card was in its typing form was fitted around the wrong card
            if (this._refitAfterTyping && this.family && !this.inView()) this.fit();
            this._refitAfterTyping = false;
          }, 120);
        });
        this["hide_" + which] = () => { clearTimeout(timer); items = []; note = ""; render(); };
      }

      $("swap").addEventListener("click", () => {
        const a = this.state.from, b = this.state.to;
        this.setPoint("from", b, false); this.setPoint("to", a, false);
        this.recompute("auto");
      });
      for (const btn of $("mode").querySelectorAll("button")) {
        btn.addEventListener("click", async () => {
          if (this.state.mode === btn.dataset.v) return;
          this.state.mode = btn.dataset.v;
          for (const b of $("mode").querySelectorAll("button")) b.setAttribute("aria-pressed", b === btn ? "true" : "false");
          // endpoints may sit on steps or a footpath a bike cannot use: re-snap, and move the pins too
          const seqs = { from: ++this._seq.from, to: ++this._seq.to };
          const snapped = await Promise.all(["from", "to"].map(async (w) => {
            const p = this.state[w];
            if (!p) return null;
            const r = await this.snap(p.lon, p.lat);
            return r.error ? p : Object.assign({}, p, { lon: r.lon, lat: r.lat, node: r.node });
          }));
          if (seqs.from !== this._seq.from || seqs.to !== this._seq.to) return;
          this.state.from = snapped[0]; this.state.to = snapped[1];
          this.drawMarkers();
          this.recompute(false);
        });
      }
      for (const btn of $("units").querySelectorAll("button")) {
        btn.addEventListener("click", () => {
          if (this.units.system === btn.dataset.v) return;
          this.units = makeUnits(btn.dataset.v);
          store.set(UNITS_KEY, btn.dataset.v);
          this.applyUnits();
        });
      }
      const sl = $("sl");
      sl.addEventListener("input", () => { this.state.t = +sl.value; this.show(); this.writeHashSoon(); });
      sl.addEventListener("change", () => this.writeHash());
      // arrow keys step one route at a time once the family is in
      sl.addEventListener("keydown", (e) => {
        const f = this.family;
        if (!f || f.partial || f.unique.length < 2) return;
        const d = { ArrowRight: 1, ArrowUp: 1, ArrowLeft: -1, ArrowDown: -1 }[e.key];
        if (!d) return;
        e.preventDefault();
        const n = f.unique.length, step = clamp(this.stepAt(this.state.t) + d, 0, n - 1);
        this.state.t = step / (n - 1); sl.value = this.state.t;
        this.show(); this.writeHashSoon();
      });
      $("share").addEventListener("click", () => {
        const url = this.shareUrl(), box = $("sharebox"), btn = $("share");
        const done = () => { btn.textContent = "Link copied"; clearTimeout(this._copied); this._copied = setTimeout(() => { btn.textContent = "Copy link"; }, 1800); };
        const fallback = () => { box.value = url; box.hidden = false; box.focus(); box.select(); };
        if (navigator.clipboard && navigator.clipboard.writeText) {
          navigator.clipboard.writeText(url).then(done, fallback);
        } else fallback();
      });
      const onResize = () => {
        if (this.shown) this.drawProfile(this.shown, this.shown, 1);
        if (this.map) this.layoutAttribution();
        if (this.mapLabels && this.mapLabels._map) this.mapLabels._update();  // the card moved or grew
        const card = $("card");
        if (card.classList.contains("typing")) return;
        this._dockH = card.offsetHeight;
        document.documentElement.style.setProperty("--card-h", this._dockH + "px");
      };
      window.addEventListener("resize", onResize);
      // Back, Forward, or a link pasted over the current one. One Back can fire both events,
      // so each URL is handled once; our own pushState/replaceState writes fire neither.
      const onUrl = async () => {
        let h = "";
        try { h = location.hash; } catch (e) { return; }
        if (h === this._urlSeen) return;
        this._urlSeen = h;
        if (this.state.from && this.state.to && h === "#" + this.token()) return;
        if (await this.readHash()) this.recompute(true);
      };
      window.addEventListener("popstate", onUrl);
      window.addEventListener("hashchange", onUrl);
      if (window.ResizeObserver) new ResizeObserver(onResize).observe($("card"));
      onResize();
    },
    hideSuggest(which) { if (this["hide_" + which]) this["hide_" + which](); },
    applyUnits() {
      for (const b of $("units").querySelectorAll("button")) b.setAttribute("aria-pressed", b.dataset.v === this.units.system ? "true" : "false");
      if (this.shown && this.family) {
        this.writeStats(this.shown, this.shown, 1);
        this.drawDelta(this.shown);
        this.drawProfile(this.shown, this.shown, 1);
      }
    },

    /* ------------------------------------------------------------ routing */
    recompute(fit) {
      const { from, to, mode } = this.state;
      if (this.worker && this._gen) this.worker.postMessage({ type: "cancel", gen: this._gen });
      this.family = null;
      const gen = ++this._gen;
      this._fit = fit;
      this._moved = false;  // set when the user pans or zooms; then the answer no longer moves the map
      if (!from || !to) {
        this.clearRoute();
        setStatus(!from && !to ? "Type two places, or click the map twice."
          : (!from ? "Where are you starting from?" : "Where to?"));
        return;
      }
      if (from.node === to.node) { this.clearRoute(); setStatus("Those are the same junction."); return; }
      // the old route stays, faded, until the new one arrives
      this.familyLayer.clearLayers();
      if (this._line) { this._line.setStyle({ opacity: 0.35 }); this._casing.setStyle({ opacity: 0.3 }); }
      $("sl").disabled = true;
      setStatus("Finding the shortest and flattest routes…");
      // a long trip can take a while to load: show both ends now, the routes when they come
      const ends = L.latLngBounds([[from.lat, from.lon], [to.lat, to.lon]]);
      if (fit === true || (fit === "auto" && !this.inView(ends))) this.fit(ends.pad(0.15));
      this._routing = gen;
      this.worker.postMessage({ type: "route", gen,
        from: { node: from.node, lon: from.lon, lat: from.lat },
        to: { node: to.node, lon: to.lon, lat: to.lat }, mode });
    },
    onProgress(m) {
      const pct = (d, t) => Math.round(100 * clamp(d / t, 0, 1)) + "%";
      if (m.stage === "tiles") {
        setStatus("Loading the street network… " + (m.total ? pct(m.done, m.total) : (m.done / 1e6).toFixed(1) + " MB"));
        return;
      }
      setStatus("Finding every route between shortest and flattest… "
        + (m.solutions !== undefined ? m.solutions : m.total ? pct(m.done, m.total) : m.done));
    },
    onRouteError(m) {
      const stale = m.stale || m.code === "stale" || (m.code === "internal" && /\b404\b/.test(m.message || ""));
      if (stale && this._recoveredFor !== this._gen) {
        this._recoveredFor = this._gen + 1;  // the retry's generation (recover() sends it)
        this.recover().then((ok) => { if (!ok) this.routeFailed(m); }, () => this.routeFailed(m));
        return;
      }
      this.routeFailed(m);
    },
    routeFailed(m) {
      this.clearRoute();
      const bike = this.state.mode === "bike";
      const msg = {
        same: "Those are the same junction.",
        unreachable: bike ? "No bikeable route between those points." : "No route between those points.",
        nobike: "No bikeable route between those points.",
      }[m.code] || ("Something went wrong: " + (m.message || m.code));
      setStatus(msg, m.code === "internal");
    },

    /* worker Member -> what the page draws */
    member(m, id) {
      const f = m.latlngs, pts = new Array(f.length >> 1);
      for (let k = 0; k < pts.length; k++) pts[k] = [f[2 * k], f[2 * k + 1]];
      return { id, length_m: m.length_m, gain_m: m.gain_m, loss_m: m.loss_m, max_grade: m.max_grade,
        latlngs: pts, profile: m.profile_z, runs: m.runs || [] };
    },
    onFamily(m) {
      const members = m.members.map((x, i) => this.member(x, i));
      if (!members.length) { this.routeFailed({ code: "unreachable" }); return; }
      if (m.info) console.debug("route", m.partial ? "partial" : "final", m.info);
      if (!m.partial) { this.lastInfo = m.info || null; this._routing = 0; }  // timings, for tests and the console
      // the worker re-snaps an endpoint the mode cannot use: move its pin to where the route starts
      if (m.ends && m.ends.length === 2) {
        let moved = false;
        ["from", "to"].forEach((w, k) => {
          const p = this.state[w], e = m.ends[k];
          if (p && e && e.node !== p.node && Number.isFinite(e.lon)) {
            this.state[w] = Object.assign({}, p, { node: e.node, lon: e.lon, lat: e.lat });
            moved = true;
          }
        });
        if (moved) this.drawMarkers();
      }
      const first = !this.family;
      // the final member at the slider is often the provisional one: keep it shown, no crossfade
      if (this.shown) {
        const same = members.find((u) => sameRoute(u, this.shown));
        if (same) this.shown = same;
      }
      this.family = { unique: members, shortest: members[0], partial: !!m.partial, truncated: !!m.truncated };
      const n = members.length;
      if (m.partial) {
        setStatus("Finding every route between shortest and flattest…");
        $("sl").disabled = true;
      } else {
        $("sl").disabled = false;
        setStatus(this.familyStatus());
      }
      this.drawFamily();
      this.show(first);
      if (first) {
        this.writeHash();
        $("share").hidden = false; $("sharebox").hidden = true;
      }
      if (m.partial || first) {
        if (!this._moved && (this._fit === true || (this._fit === "auto" && !this.inView()))) this.fit();
      } else if (this._fit && !this._moved && !this.inView()) this.fit();
    },

    familyStatus() {
      const f = this.family, n = f.unique.length;
      return n === 1 ? "One route: the shortest is already the flattest."
        : n + " distinct routes, from shortest to flattest."
          + (f.truncated ? " This long trip stopped the search early, so there may be more in between." : "");
    },

    clearRoute() {
      this._routing = 0;
      this.familyLayer.clearLayers(); this.routeLayer.clearLayers(); this.labelLayer.clearLayers();
      this._line = this._casing = null;
      this._labelled = null;
      this.mapLabels.setAvoid([]);
      if (this._profAnim) cancelAnimationFrame(this._profAnim);
      this._statsTok = (this._statsTok || 0) + 1;
      $("turns").hidden = true;
      this.shown = null;
      $("result").hidden = true; $("prof").hidden = true; $("delta").textContent = ""; $("slpos").textContent = "";
      $("share").hidden = true; $("sharebox").hidden = true;
      $("sl").disabled = false;
      $("sl").removeAttribute("aria-valuetext");
    },

    /* slider position -> index into the family, evenly over its members */
    stepAt(t) {
      const n = this.family.unique.length;
      return clamp(Math.round(t * (n - 1)), 0, n - 1);
    },

    drawFamily() {
      this.familyLayer.clearLayers();
      for (const u of this.family.unique) {
        L.polyline(u.latlngs, { color: css("--family"), weight: 2, opacity: 0.45, interactive: false,
          lineJoin: "round", lineCap: "round" }).addTo(this.familyLayer);
      }
    },

    /* show the family member for the current slider position */
    show(immediate) {
      if (!this.family) return;
      const t = this.state.t, step = this.stepAt(t), n = this.family.unique.length;
      const u = this.family.unique[step];
      const colour = ramp(t);
      $("slpos").textContent = this.family.partial ? "" : (n === 1 ? "" : (step + 1) + " of " + n);
      if (!this.family.partial && n > 1) $("sl").setAttribute("aria-valuetext", "Route " + (step + 1) + " of " + n);
      const prev = this.shown;
      if (prev === u && this._line) {
        this.tintRoute(colour);
        // new family lines were added above it
        this._casing.bringToFront(); this._line.bringToFront();
        this.drawDelta(u);
        return;
      }
      this.shown = u;
      const from = prev && !immediate ? prev : null;
      this.drawRoute(u, colour, from);
      this.drawStats(u, from || u);
      this.animateProfile(from || u, u);
    },

    tintRoute(colour) {
      if (this._line) this._line.setStyle({ color: colour, opacity: 1 });
      if (this._casing) this._casing.setStyle({ opacity: 0.9 });
      $("prof").dataset.colour = colour;
      if (this.shown) this.drawProfile(this.shown, this.shown, 1);
    },

    drawRoute(u, colour, prev) {
      // crossfade: the old line fades out while the new one fades in
      const casing = css("--route-casing");
      if (this._line && prev) {
        const oldCase = this._casing, oldLine = this._line;
        fadeOut([oldCase, oldLine], 260, () => { this.routeLayer.removeLayer(oldCase); this.routeLayer.removeLayer(oldLine); });
      } else {
        this.routeLayer.clearLayers();
      }
      this._casing = L.polyline(u.latlngs, { color: casing, weight: 10, opacity: prev ? 0 : 0.9, interactive: false,
        lineJoin: "round", lineCap: "round" }).addTo(this.routeLayer);
      this._line = L.polyline(u.latlngs, { color: colour, weight: 5, opacity: prev ? 0 : 1, interactive: false,
        lineJoin: "round", lineCap: "round" }).addTo(this.routeLayer);
      if (prev) fadeIn([[this._casing, 0.9], [this._line, 1]], 260);
      this._casing.bringToFront(); this._line.bringToFront();
      $("prof").dataset.colour = colour;
      this.labelRoute(u);
      this.mapLabels.setAvoid([u.latlngs]);
    },

    /* Street names drawn along the highlighted route: one per named run of
     * 80 m or more, rotated to the street's bearing at its middle, only
     * where the run is long enough on screen to carry its text, never
     * overlapping another label. Redrawn on zoom, since what fits changes. */
    labelRoute(u) {
      this.labelLayer.clearLayers();
      this._labelled = u;
      if (!u) return;
      const map = this.map, z = map.getZoom();
      const runs = namedRuns(u.runs, 80).filter((r) => r.mid).sort((a, b) => b.length_m - a.length_m);
      const placed = [];
      for (const r of runs) {
        if (placed.length >= 10) break;
        const text = shortStreet(r.name);
        const mpp = 156543.03392 * Math.cos(r.mid[0] * Math.PI / 180) / Math.pow(2, z);
        const need = text.length * 6.6 + 28;
        if (r.length_m / mpp < need) continue;
        const mid = map.latLngToContainerPoint(r.mid), size = map.getSize();
        // off-screen labels would use up the budget of ten
        if (mid.x < need / 2 || mid.y < 10 || mid.x > size.x - need / 2 || mid.y > size.y - 10) continue;
        if (placed.some((q) => q.distanceTo(mid) < need * 0.6)) continue;
        // compass bearing -> screen angle, folded so text is never upside down
        let deg = ((r.bearing || 0) - 90) % 360;
        if (deg > 180) deg -= 360; else if (deg <= -180) deg += 360;
        if (deg > 90) deg -= 180; else if (deg < -90) deg += 180;
        const m = L.marker(r.mid, { interactive: false, keyboard: false,
          icon: L.divIcon({ className: "rtlabel", iconSize: null,
            html: `<span style="--rot:${deg.toFixed(1)}deg"></span>` }) }).addTo(this.labelLayer);
        m.getElement().firstChild.textContent = text;
        placed.push(mid);
      }
    },

    drawStats(u, prevU) {
      $("result").hidden = false;
      const runs = namedRuns(u.runs, 60);
      const box = $("turns");
      const render = (all) => {
        box.innerHTML = "";
        const show = all || runs.length <= 8 ? runs : runs.slice(0, 7);
        show.forEach((r, i) => {
          if (i) {
            const v = document.createElement("span"); v.className = "via"; v.textContent = "→";
            box.appendChild(v); box.appendChild(document.createElement("wbr"));
          }
          const st = document.createElement("span");
          st.className = "st"; st.textContent = shortStreet(r.name);
          box.appendChild(st);
        });
        if (show.length < runs.length) {
          const more = document.createElement("button");
          more.type = "button"; more.className = "link more";
          more.textContent = "+" + (runs.length - show.length) + " more";
          more.addEventListener("click", () => render(true));
          box.appendChild(more);
        }
      };
      render(false);
      box.hidden = runs.length === 0;
      const tok = this._statsTok = (this._statsTok || 0) + 1;
      tween(260, (k) => { if (tok === this._statsTok) this.writeStats(prevU, u, k); });
      this.drawDelta(u);
    },
    writeStats(p, s, k) {
      const U = this.units;
      $("v_dist").innerHTML = U.dist(lerp(p.length_m, s.length_m, k));
      $("v_climb").innerHTML = U.climb(lerp(p.gain_m, s.gain_m, k));
      $("v_grade").innerHTML = fmtPct(lerp(p.max_grade, s.max_grade, k));
    },
    drawDelta(u) {
      const U = this.units, f = this.family;
      if (!f) return;
      const sh = f.shortest;
      if (u === sh) {
        $("delta").innerHTML = f.unique.length > 1
          ? "The shortest route. Slide right to trade distance for less climbing."
          : "Shortest and flattest at once.";
        return;
      }
      const dd = u.length_m - sh.length_m, dc = sh.gain_m - u.gain_m;
      const pd = sh.length_m ? Math.round(100 * dd / sh.length_m) : 0;
      const pc = sh.gain_m ? Math.round(100 * dc / sh.gain_m) : 0;
      const longer = dd < 80 ? "about the same distance"
        : "<b class='up'>" + U.deltaDist(dd) + "</b> (" + pd + "% longer)";
      const less = dc <= 0 || U.deltaClimb(dc) === U.deltaClimb(0) ? "no less climbing"
        : "<b class='down'>" + U.deltaClimb(dc) + "</b> of climbing (" + pc + "% less)";
      $("delta").innerHTML = "vs. shortest: " + longer + ", " + less;
    },

    /* ------------------------------------------------------------ profile */
    animateProfile(a, b) {
      $("prof").hidden = false;
      if (this._profAnim) cancelAnimationFrame(this._profAnim);
      const t0 = performance.now();
      const frame = (now) => {
        if (!this.family) return;
        const k = clamp((now - t0) / 300, 0, 1);
        this.drawProfile(a, b, ease(k));
        if (k < 1) this._profAnim = requestAnimationFrame(frame);
      };
      this._profAnim = requestAnimationFrame(frame);
    },

    drawProfile(a, b, k) {
      if (!this.family || !b.profile) return;
      const cv = $("prof"), dpr = window.devicePixelRatio || 1;
      const W = cv.clientWidth || 360, H = cv.clientHeight || 92;
      if (cv.width !== W * dpr || cv.height !== H * dpr) { cv.width = W * dpr; cv.height = H * dpr; }
      const ctx = cv.getContext("2d");
      ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
      ctx.clearRect(0, 0, W, H);
      const n = b.profile.length;
      const z = new Float64Array(n);
      const ap = a.profile && a.profile.length === n ? a.profile : b.profile;
      for (let i = 0; i < n; i++) z[i] = lerp(ap[i], b.profile[i], k);
      const dist = lerp(a.length_m, b.length_m, k);
      // a fixed vertical scale across the family keeps the hills comparable
      let zmin = Infinity, zmax = -Infinity;
      for (const u of this.family.unique) for (const v of u.profile) { if (v < zmin) zmin = v; if (v > zmax) zmax = v; }
      const span = Math.max(zmax - zmin, 15);
      zmin -= span * 0.08; zmax = zmin + span * 1.2;
      const padL = 6, padR = 6, top = 8, bottom = 18;
      const X = (i) => padL + (W - padL - padR) * i / (n - 1);
      const Y = (v) => top + (H - top - bottom) * (1 - (v - zmin) / (zmax - zmin));
      const colour = cv.dataset.colour || css("--route");
      ctx.beginPath();
      ctx.moveTo(X(0), Y(zmin));
      for (let i = 0; i < n; i++) ctx.lineTo(X(i), Y(z[i]));
      ctx.lineTo(X(n - 1), Y(zmin)); ctx.closePath();
      ctx.fillStyle = colour; ctx.globalAlpha = 0.18; ctx.fill(); ctx.globalAlpha = 1;
      ctx.beginPath();
      for (let i = 0; i < n; i++) { if (i) ctx.lineTo(X(i), Y(z[i])); else ctx.moveTo(X(i), Y(z[i])); }
      ctx.strokeStyle = colour; ctx.lineWidth = 2; ctx.lineJoin = "round"; ctx.stroke();
      // labels: start and end elevation, the high point, the distance scale
      ctx.fillStyle = css("--muted"); ctx.font = "500 10px " + css("--mono");
      ctx.textBaseline = "alphabetic";
      let hi = 0; for (let i = 1; i < n; i++) if (z[i] > z[hi]) hi = i;
      const U = this.units;
      ctx.textAlign = "left"; ctx.fillText(U.elev(z[0]), padL, H - 5);
      ctx.textAlign = "right"; ctx.fillText(U.elev(z[n - 1]), W - padR, H - 5);
      ctx.textAlign = "center"; ctx.fillText(U.span(dist), W / 2, H - 5);
      if (hi > n * 0.06 && hi < n * 0.94 && z[hi] - Math.min(z[0], z[n - 1]) > 6) {
        ctx.textAlign = X(hi) < 40 ? "left" : X(hi) > W - 40 ? "right" : "center";
        ctx.fillStyle = css("--ink");
        ctx.fillText(U.elev(z[hi]), X(hi), Math.max(10, Y(z[hi]) - 5));
      }
    },

    familyBounds() {
      const b = L.latLngBounds([]);
      for (const u of this.family.unique) for (const ll of u.latlngs) b.extend(ll);
      return b;
    },
    narrow() { return this.map ? this.map.getSize().x <= 640 : window.innerWidth <= 640; },
    /* what floats over the map, in map container pixels: no map label goes under it */
    obstacles() {
      const m = this.map.getContainer().getBoundingClientRect(), out = [];
      for (const el of document.querySelectorAll("#card, .credit, .leaflet-control-attribution, .leaflet-control-zoom")) {
        const r = el.getBoundingClientRect();
        if (r.width && r.height) out.push([r.left - m.left - 4, r.top - m.top - 4, r.right - m.left + 4, r.bottom - m.top + 4]);
      }
      return out;
    },
    /* the card as it covers the map; on a phone, docked (not its typing form at the top) */
    cardBox() {
      const r = $("card").getBoundingClientRect();
      if (!this.narrow() || !$("card").classList.contains("typing")) return { right: r.right, top: r.top, height: r.height };
      const H = this.map.getSize().y, h = this._dockH || 0.58 * H;
      return { right: r.right, top: H - h, height: h };
    },
    /* is the whole family (or bounds b) inside the part of the map the card does not cover? */
    inView(b) {
      if (!b && !this.family) return true;
      b = b || this.familyBounds();
      const map = this.map, size = map.getSize(), card = this.cardBox();
      const sw = map.latLngToContainerPoint(b.getSouthWest()), ne = map.latLngToContainerPoint(b.getNorthEast());
      // a few pixels looser than fit()'s padding, so a family just fitted counts as in view
      const wide = size.x > 640, m = 12;
      const x0 = wide ? card.right + m : m, y1 = wide ? size.y - m : card.top - m;
      return sw.x >= x0 && ne.x <= size.x - m && ne.y >= m + this.topInset() && sw.y <= y1;
    },
    /* fit the family (or bounds b) into the part of the map the card leaves free */
    fit(b) {
      if (!b && !this.family) return;
      b = b || this.familyBounds();
      // Leaflet drops a view change that arrives during its zoom animation: fit once it ends
      if (this.map._animatingZoom) {
        const again = !this._fitAfter;
        this._fitAfter = b;
        if (again) this.map.once("zoomend", () => { const nb = this._fitAfter; this._fitAfter = null; this.fit(nb); });
        return;
      }
      const size = this.map.getSize();
      const wide = size.x > 640;
      const card = this.cardBox();
      this.map.fitBounds(b, wide
        ? { paddingTopLeft: [card.right + 24, 24], paddingBottomRight: [40, 40], maxZoom: 15 }
        : { paddingTopLeft: [16, 16 + this.topInset()], paddingBottomRight: [16, card.height + 16], maxZoom: 15 });
    },
    /* on a phone the attribution sits at the top of the map */
    topInset() {
      if (!this._attrCompact) return 0;
      const el = this.map.attributionControl.getContainer();
      return el ? el.offsetHeight : 0;
    },

    /* ------------------------------------------------------------ sharing */
    token() { return makeToken(this.state); },
    /* A new trip (either end or the mode) gets its own history entry, so Back returns to the
     * trip before it. Slider moves, and the re-snapped form of a link just restored, only
     * update the entry they are on. */
    writeHash() {
      clearTimeout(this._hashTimer);
      const { from, to } = this.state;
      if (!from || !to) return;
      const key = tripKey(this.state);
      let onTrip = false;
      try { onTrip = parseToken(location.hash) !== null; } catch (e) { /* sandboxed */ }
      const push = onTrip && this._urlTrip !== undefined && key !== this._urlTrip;
      this._urlTrip = key;
      const h = "#" + this.token();
      this._urlSeen = h;
      try { history[push ? "pushState" : "replaceState"](null, "", h); } catch (e) { /* sandboxed */ }
    },
    /* browsers throttle replaceState, so a slider drag writes once it settles */
    writeHashSoon() {
      clearTimeout(this._hashTimer);
      this._hashTimer = setTimeout(() => this.writeHash(), 250);
    },
    shareUrl() {
      let base = "";
      try { base = location.href.split("#")[0]; } catch (e) { /* sandboxed */ }
      return base + "#" + this.token();
    },
    async readHash() {
      let h = "";
      try { h = location.hash; } catch (e) { return false; }
      const tok = parseToken(h);
      if (!tok) return false;
      this.state.mode = tok.mode;
      for (const b of $("mode").querySelectorAll("button")) b.setAttribute("aria-pressed", b.dataset.v === tok.mode ? "true" : "false");
      if (tok.t !== null) { this.state.t = tok.t; $("sl").value = tok.t; }
      setStatus("Loading the street network…");
      // coordinates are re-snapped, so links survive graph rebuilds
      const [a, b] = await Promise.all([
        this.pointAt(tok.from.lon, tok.from.lat, tok.from.label || undefined),
        this.pointAt(tok.to.lon, tok.to.lat, tok.to.label || undefined)]);
      if (a.error && b.error) return false;
      // a newer Back or Forward arrived while the ends were loading: that one wins
      try { if (location.hash !== h) return false; } catch (e) { /* sandboxed */ }
      this.setPoint("from", a.error ? null : a, false);
      this.setPoint("to", b.error ? null : b, false);
      this._urlTrip = this.state.from && this.state.to ? tripKey(this.state) : undefined;
      return true;
    },
  };

  function sameRoute(a, b) {
    return a.latlngs.length === b.latlngs.length && Math.abs(a.length_m - b.length_m) < 0.01
      && Math.abs(a.gain_m - b.gain_m) < 0.01;
  }
  function tween(ms, fn) {
    const t0 = performance.now();
    const frame = (now) => { const k = clamp((now - t0) / ms, 0, 1); fn(ease(k)); if (k < 1) requestAnimationFrame(frame); };
    requestAnimationFrame(frame);
  }
  function fadeOut(layers, ms, done) {
    const start = layers.map((l) => l.options.opacity);
    tween(ms, (k) => { layers.forEach((l, i) => l.setStyle({ opacity: start[i] * (1 - k) })); if (k >= 1) done(); });
  }
  function fadeIn(pairs, ms) {
    tween(ms, (k) => { pairs.forEach(([l, o]) => l.setStyle({ opacity: o * k })); });
  }

  root.App = App;
  App.start().catch((err) => {
    console.error(err);
    setStatus("Could not start: " + err.message, true);
  });
})(typeof window !== "undefined" ? window : globalThis);
