/* Isnad analysis core — JS port of parser.py + engine (v0.2.1)
   Works in browser and Node (for tests). */
(function (root) {
  "use strict";

  const DIAC = /[ً-ٰۖ-ۭـ]/g;
  function norm(s) {
    s = (s || "").replace(DIAC, "");
    s = s.replace(/[أإآٱ]/g, "ا").replace(/ة/g, "ه").replace(/ى/g, "ي");
    s = s.replace(/[^ء-ي ]/g, " ");
    return s.replace(/\s+/g, " ").trim();
  }

  const VERBS = ["حدثنا","حدثني","حدثتنا","حدثته","اخبرنا","اخبرني","اخبرته","انبانا","انباني",
                 "سمعت","سمعنا","عن","قال","قالت","قالا","قالوا","يقول","ان","انه","انها","نا","ثنا","اننا"];
  const VERB_SET = new Set(VERBS);
  const SARIH = new Set(["حدثنا","حدثني","حدثتنا","حدثته","اخبرنا","اخبرني","اخبرته","انبانا","انباني","سمعت","سمعنا","نا","ثنا"]);
  const TRAIL = new Set(["اخبره","اخبرته","حدثه","حدثته","انه","انها","يقول","قال","قالت","سمعه","يحدث","ذكر"]);
  const LINKERS = new Set(["بن","ابن","ابو","ابي","ام","بنت","ابنه","مولي"]);
  const HONOR = /(رضي الله عن(ه|ها|هم|هما)|رحمه الله|عليه السلام|صلي الله عليه وسلم)/g;
  const PROPHET = /(النبي|رسول الله|نبي الله)/;
  const NOISE = /^(و|ح|قال|يقول|انه|ذكر|سمع|هو|هي|وهو)$/;

  function classifyVerb(v) {
    if (SARIH.has(v)) return { label: "صريح السماع", status: "ok" };
    if (v === "عن") return { label: "معنعن", status: "check" };
    if (v === "ان") return { label: "مؤنأن", status: "check" };
    return { label: v ? "(" + v + ")" : "غير محددة", status: "neutral" };
  }

  function splitNames(isnadText) {
    let t = norm(isnadText);
    let tahwil = false;
    const m = t.split(/(?:^| )ح(?: |$)/);
    if (m.length > 1) { tahwil = true; t = m[0]; }
    const tokens = t.split(" ").filter(Boolean);
    const segs = [];
    let cur = [], curVerb = null;
    for (const tok of tokens) {
      const base = (tok.startsWith("و") && VERB_SET.has(tok.slice(1))) ? tok.slice(1) : tok;
      if (VERB_SET.has(base)) {
        if (cur.length) { segs.push([cur.join(" "), curVerb]); cur = []; }
        curVerb = base;
      } else cur.push(tok);
    }
    if (cur.length) segs.push([cur.join(" "), curVerb]);

    const out = [];
    for (let [name, verb] of segs) {
      name = name.replace(HONOR, "").replace(/\s+/g, " ").trim();
      if (!name || NOISE.test(name)) continue;
      if (PROPHET.test(name)) break;
      let toks = name.split(" ");
      while (toks.length && TRAIL.has(toks[toks.length - 1])) toks.pop();
      // co-narrator split
      const parts = []; let cur2 = [];
      for (let j = 0; j < toks.length; j++) {
        const tk = toks[j], prev = j ? toks[j - 1] : null;
        if (j && tk.startsWith("و") && tk.length > 2 && !LINKERS.has(prev) && cur2.length) {
          parts.push(cur2.join(" ")); cur2 = [tk.slice(1)];
        } else if (tk === "و" && cur2.length) {
          parts.push(cur2.join(" ")); cur2 = [];
        } else cur2.push(tk);
      }
      if (cur2.length) parts.push(cur2.join(" "));
      const clean = parts.filter(Boolean);
      if (!clean.length) continue;
      const flags = [];
      if (clean.length > 1) flags.push("co:" + clean.slice(1).join("؛"));
      if (tahwil) { flags.push("tahwil"); tahwil = false; }
      out.push({ mention: clean[0], verb: verb, flags: flags });
    }
    return out;
  }

  // ---------- Matcher ----------
  function Matcher(mentionDict, profilesRaw, kaggle) {
    this.dict = mentionDict; // {normform: [[id,count],...]}
    this.profiles = {};
    const vals = Array.isArray(profilesRaw) ? profilesRaw : Object.values(profilesRaw);
    for (const v of vals) this.profiles[v.id] = v;
    this.nameTokens = {};
    for (const [pid, p] of Object.entries(this.profiles)) {
      const full = norm((p.data && p.data["الاسم"]) || "") + " " + norm(p.name);
      this.nameTokens[pid] = new Set(full.split(" ").filter(Boolean));
    }
    this.kaggle = kaggle || {};
    this.kTokens = {};
    for (const [kid, v] of Object.entries(this.kaggle))
      this.kTokens[kid] = new Set(norm(v.name_ar).split(" ").filter(Boolean));
  }

  Matcher.prototype.match = function (mention) {
    const m = norm(mention);
    if (this.dict[m]) {
      const entries = this.dict[m];
      const total = entries.reduce((a, e) => a + e[1], 0);
      const [best, n] = entries[0];
      if (n / total >= 0.9 && total >= 2)
        return { id: best, src: "db", conf: "high", via: "dict", candidates: [] };
      return { id: n / total >= 0.6 ? best : null, src: "db", conf: "ambiguous", via: "dict",
               candidates: entries.slice(0, 4).map(e => ({ id: e[0], src: "db", share: e[1] / total })) };
    }
    const mt = m.split(" ").filter(w => w && w !== "بن" && w !== "ابن");
    if (!mt.length) return { id: null, conf: "none", candidates: [] };
    const mset = new Set(mt);
    const score = (ts) => {
      let inter = 0; for (const w of mset) if (ts.has(w)) inter++;
      return inter === mset.size ? inter / Math.sqrt(ts.size) : 0;
    };
    let scored = [];
    for (const [pid, ts] of Object.entries(this.nameTokens)) {
      const s = score(ts); if (s > 0) scored.push([s, pid, "db"]);
    }
    if (!scored.length)
      for (const [kid, ts] of Object.entries(this.kTokens)) {
        const s = score(ts); if (s > 0) scored.push([s, kid, "registry"]);
      }
    scored.sort((a, b) => b[0] - a[0]);
    if (scored.length) {
      const conf = scored.length === 1 ? "medium" : "ambiguous";
      return { id: scored[0][1], src: scored[0][2],
               conf: conf, via: scored[0][2] === "db" ? "fuzzy" : "registry",
               candidates: scored.slice(0, 4).map(x => ({ id: x[1], src: x[2], score: Math.round(x[0] * 100) / 100 })) };
    }
    return { id: null, conf: "none", candidates: [] };
  };

  function isCompanion(prof) {
    const d = prof.data || {};
    const t = (d["طبقة رواة التقريب"] || "").trim();
    const r = (d["الرتبة عند ابن حجر"] || "").trim();
    return t.startsWith("صحابي") || t.startsWith("صحابية") || r.startsWith("صحابي") || r.startsWith("صحابية");
  }

  function analyzeChain(isnadText, matcher) {
    const chain = splitNames(isnadText);
    const items = [], flags = [];
    chain.forEach((x, i) => {
      const r = matcher.match(x.mention);
      const verb = x.verb || "؟";
      const sig = classifyVerb(x.verb);
      const item = { idx: i + 1, mention: x.mention, verb: verb, sigha: sig, match: r };
      if (r.id != null && (r.conf === "high" || r.conf === "medium")) {
        if (r.src === "db") {
          item.profile = matcher.profiles[r.id];
          item.companion = isCompanion(item.profile);
          const blob = JSON.stringify(item.profile.data || {});
          if (/يدلس|تدليس|مدلس/.test(blob) && !item.companion)
            flags.push({ who: x.mention, msg: "موصوف بالتدليس — إن روى بالعنعنة يُبحث عن تصريحه بالسماع في الطرق الأخرى [R3]" });
        } else item.registry = matcher.kaggle[r.id];
      }
      if (sig.status === "check" && i > 0)
        flags.push({ who: chain[i - 1].mention, msg: `روايته عن ${x.mention} بصيغة «${verb}» — عنعنة: يُتحقق من الاتصال [R3]` });
      for (const f of x.flags) {
        if (f.startsWith("co:")) flags.push({ who: x.mention, msg: "معه في نفس الطبقة: " + f.slice(3) + " (لم يُحلَّل آليًا)" });
        if (f === "tahwil") flags.push({ who: x.mention, msg: "في الإسناد تحويل (ح) — حُلِّل الطريق الأول فقط" });
      }
      items.push(item);
    });
    return { items, flags };
  }

  const API = { norm, splitNames, classifyVerb, Matcher, analyzeChain, isCompanion };
  if (typeof module !== "undefined" && module.exports) module.exports = API;
  else root.IsnadCore = API;
})(typeof window !== "undefined" ? window : globalThis);
