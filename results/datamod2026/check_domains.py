"""Check the computed domains in results.json (written by analyze.py).

A10: every conjunct should be a side condition of the form `e ≠ 0`.
A9:  every domain should be satisfiable. A domain is reported satisfiable when some
     sample point satisfies all of its conjuncts, evaluated with Mathlib's conventions
     (x / 0 = 0, log x = log |x| with log 0 = 0, tan x = sin x / cos x).
usage: python3 check_domains.py <dir with results.json>
"""
import json, math, re, sys

D = sys.argv[1] if len(sys.argv) > 1 else "."
r = json.load(open(f"{D}/results.json"))


def conjuncts(pred):
    """Top-level conjuncts of `fun x => A ∧ B ∧ ...`, flattening nested conjunctions."""
    body = pred[len("fun x => "):] if pred.startswith("fun x => ") else pred
    out, depth, cur, i = [], 0, "", 0
    while i < len(body):
        c = body[i]
        depth += c == "("
        depth -= c == ")"
        if depth == 0 and body.startswith(" ∧ ", i):
            out.append(cur); cur = ""; i += 3; continue
        cur += c; i += 1
    out.append(cur)
    res = []
    for c in (c.strip() for c in out):
        if c.startswith("(") and c.endswith(")") and " ∧ " in c and balanced(c[1:-1]):
            res += conjuncts(c[1:-1])
        else:
            res.append(c)
    return res


def balanced(s):
    d = 0
    for c in s:
        d += c == "("; d -= c == ")"
        if d < 0:
            return False
    return d == 0


class R(float):
    """A real number with Mathlib's total operations."""
    def __add__(a, b): return R(float(a) + float(b))
    __radd__ = __add__
    def __sub__(a, b): return R(float(a) - float(b))
    def __rsub__(a, b): return R(float(b) - float(a))
    def __mul__(a, b): return R(float(a) * float(b))
    __rmul__ = __mul__
    def __truediv__(a, b): return R(0.0 if float(b) == 0 else float(a) / float(b))
    def __rtruediv__(a, b): return R(0.0 if float(a) == 0 else float(b) / float(a))
    def __pow__(a, n): return R(float(a) ** int(n))
    def __neg__(a): return R(-float(a))


def LOG(v): return R(0.0 if float(v) == 0 else math.log(abs(float(v))))
def SIN(v): return R(math.sin(float(v)))
def COS(v): return R(math.cos(float(v)))
def TAN(v): return R(COS(v) and SIN(v) / COS(v))


def compile_expr(e):
    """Lean expression text → Python source over R."""
    e = (e.replace("Real.sin", "SIN").replace("Real.cos", "COS")
          .replace("Real.tan", "TAN").replace("Real.log", "LOG"))
    e = re.sub(r"(SIN|COS|TAN|LOG) (x|\d+)", r"\1(\2)", e)        # f x, f 3
    e = re.sub(r"(SIN|COS|TAN|LOG) \(", r"\1(", e)
    e = re.sub(r"(?<![\w.])(\d+)(?![\w.])", r"R(\1)", e)              # literals
    e = e.replace("^", "**")
    return compile(e, "<domain>", "eval")


SAMPLES = [R(-20 + 40 * k / 3999) for k in range(4000)] + [R(v) for v in (0.5, 1.5, 2.0, 3.0, 7.0, 0.1)]

bad_form, unsat, n_const, n_dom = [], [], 0, 0
for i, v in sorted(r.items(), key=lambda kv: int(kv[0])):
    dom = v["domain"]
    if dom == "fun x => True":
        continue
    n_dom += 1
    cs = conjuncts(dom)
    if any(not re.search(r"\bx\b", c) for c in cs):
        n_const += 1
    exprs = []
    for c in cs:
        m = re.fullmatch(r"(.*) ≠ 0", c)
        if not m:
            bad_form.append((i, c)); continue
        exprs.append(compile_expr(m[1]))
    if not exprs:
        continue
    ok = any(all(eval(e, {"R": R, "SIN": SIN, "COS": COS, "TAN": TAN, "LOG": LOG, "x": x}) != 0
                 for e in exprs) for x in SAMPLES)
    if not ok:
        unsat.append((i, v["f"], dom))

print(f"restricted domains: {n_dom} of {len(r)}; with a conjunct not mentioning x: {n_const}")
print(f"A10 conjuncts not of the form `e ≠ 0`: {len(bad_form)}")
for i, c in bad_form[:20]:
    print(f"  case {i}: {c}")
print(f"A9 domains with no satisfying sample: {len(unsat)}")
for i, f, d in unsat[:20]:
    print(f"  case {i}: {f}\n     domain: {d}")
