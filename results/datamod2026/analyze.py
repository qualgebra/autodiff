"""Analyse the seeded benchmark runs in eval-data/{indexed,legacy}; writes results.json."""
import re, statistics as st, json, math, sys
D = sys.argv[1] if len(sys.argv) > 1 else "."

def load(d):
    rows = {}
    for l in open(f"{D}/{d}/log.txt"):
        l = l.strip()
        m = re.match(r"(\d+), (.*), (\d+), (\d+)((?:, (?:[\d.]+ms|FAIL))*)$", l)
        if not m:
            continue
        i = int(m[1]); ts = [x.strip() for x in m[5].split(',')[1:]]
        ok = len(ts) > 0 and all(t != 'FAIL' for t in ts)
        txt = open(f"{D}/{d}/test{i}.txt").read()
        dom = re.search(r"domain := (fun x =>.*?),\s+proof", txt, re.S)
        rows[i] = dict(f=m[2], size=int(m[3]), depth=int(m[4]), ok=ok,
                       t=st.mean(float(t[:-2]) for t in ts) if ok else None,
                       dom=' '.join(dom[1].split()) if dom else None)
    return rows

n = load('indexed'); g = load('legacy')
assert all(n[i]['f'] == g[i]['f'] for i in n), "functions differ between modes"
for r in list(n.values()) + list(g.values()):
    r['univ'] = r['dom'] == 'fun x => True' if r['dom'] else None
print("cases", len(n), len(g))
print("OK indexed", sum(r['ok'] for r in n.values()), "legacy", sum(r['ok'] for r in g.values()))
print("unparsed domains (ok cases): indexed", sum(r['ok'] and r['dom'] is None for r in n.values()),
      "legacy", sum(r['ok'] and r['dom'] is None for r in g.values()))
fails = [i for i in g if not g[i]['ok']]
print("legacy failures:", fails, "sizes", [g[i]['size'] for i in fails],
      "indexed ms", [round(n[i]['t']) for i in fails], "universal", [n[i]['univ'] for i in fails])
both = [i for i in n if n[i]['ok'] and g[i]['ok']]
diff = [i for i in both if n[i]['dom'] != g[i]['dom']]
print("domains identical:", len(both) - len(diff), "/", len(both), "differ:", diff[:20])

def pct(a, p):
    a = sorted(a); return a[min(len(a) - 1, int(p * len(a)))]
print(f"{'class':11s} {'n':>4s} | idx: med mean p95 max | legacy: med mean p95 max | speedup: med geo min max")
for name, sel in [("all", both), ("universal", [i for i in both if n[i]['univ']]),
                  ("restricted", [i for i in both if not n[i]['univ']])]:
    a = [n[i]['t'] for i in sel]; b = [g[i]['t'] for i in sel]; sp = [g[i]['t'] / n[i]['t'] for i in sel]
    geo = math.exp(st.mean(math.log(x) for x in sp))
    print(f"{name:11s} {len(sel):4d} | {st.median(a):6.1f} {st.mean(a):6.1f} {pct(a,.95):6.1f} {max(a):6.1f} | "
          f"{st.median(b):7.1f} {st.mean(b):7.1f} {pct(b,.95):7.1f} {max(b):7.1f} | "
          f"{st.median(sp):5.1f} {geo:5.1f} {min(sp):5.1f} {max(sp):6.1f}")
print(f"all indexed ({len(n)}):", f"median {st.median(r['t'] for r in n.values()):.1f} max {max(r['t'] for r in n.values()):.1f}",
      "universal", sum(r['univ'] for r in n.values()))
print("total time (both ok): indexed %.1fs legacy %.1fs" % (sum(n[i]['t'] for i in both) / 1e3, sum(g[i]['t'] for i in both) / 1e3))
print("size range", min(r['size'] for r in n.values()), max(r['size'] for r in n.values()))
print("size bucket: n, indexed median, legacy median, speedup median")
for lo, hi in [(1, 5), (6, 10), (11, 15), (16, 20), (21, 30), (31, 99)]:
    sel = [i for i in both if lo <= n[i]['size'] <= hi]
    if sel:
        print(f"  {lo:2d}-{hi:2d}: {len(sel):3d}, {st.median(n[i]['t'] for i in sel):7.1f}, "
              f"{st.median(g[i]['t'] for i in sel):8.1f}, {st.median(g[i]['t'] / n[i]['t'] for i in sel):5.1f}")
json.dump({str(i): dict(f=n[i]['f'], size=n[i]['size'], depth=n[i]['depth'], universal=n[i]['univ'],
                        domain=n[i]['dom'], t_indexed=n[i]['t'], t_legacy=g[i]['t'], legacy_ok=g[i]['ok'],
                        domain_legacy=g[i]['dom']) for i in n},
          open(f"{D}/results.json", "w"), indent=1)
