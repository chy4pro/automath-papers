#!/usr/bin/env python3
"""Exact checks. Pure integer / Fraction arithmetic, single thread, no solvers.
Run: python3 cr19b_checks.py
Part 1: every numeric inequality used in the report (exact integers).
Part 2: finite sweeps of elementary inequalities whose general proof is by induction /
        monotonicity in the report (the sweeps supplement, not replace, those proofs).
Part 3: exhaustive check of the new pattern-count Lemma 2' on small (s, B).
Part 4: sanity sweep (NOT part of the proof): hypotheses (P1)-(P3) of Proposition M
        evaluated at sample integer q with the parameters of Theorems A and B.
"""
import time, json, sys
from fractions import Fraction as F
from math import isqrt, factorial

t_start = time.process_time()
n_assert = 0
def check(ok, msg):
    global n_assert
    n_assert += 1
    if not ok:
        raise AssertionError(msg)

def ell(t):  # ceil(log2 t), integer t >= 1
    return (t - 1).bit_length()

out = {}
# ---------------- Part 1 ----------------
check(3**8 < 2**13, "(S2) 3^8 < 2^13")
# Theorem A: C = 3400, Q1 = 512*160^5
C = 3400
Q1 = 512 * 160**5
check(ell(160) == 8, "ell(160)=8")
check(C**5 * 160**5 >= 512 * 960**5 * 161**5, "(A1)")
check(C**5 >= 32 * Q1, "(A2)")
check((C + 2)**2 * 64**2 <= 2**64, "(A3)")
Cmin = 1
while Cmin**5 * 160**5 < 512 * 960**5 * 161**5:
    Cmin += 1
out["theoremA_min_integer_C_for_A1"] = Cmin
# Theorem B
QB = 49 * 575**2 * 30
check(ell(575) == 10 and QB == 486018750, "(B0) QB")
check(2**28 <= QB < 2**29, "(B0') 2^28 <= QB < 2^29")
check(575 - 23 >= 24 * 575 // 25 and 25 * (575 - 23) >= 24 * 575, "(B1) (t-23)/24 >= t/25 at t=575")
check(200**2 * 49**2 * 575**2 >= 1300**2 * 56 * 576**2, "(B2) main-branch constant 200")
check(8400**2 * 28 >= 4 * QB, "(B3) L2-branch constant 8400")
check(8402**2 * 64**2 <= 2**64, "(B4) transfer")
check(QB >= 343**2, "(B5) QB >= 343^2")
check(49 * 4**10 * 30 > 4 * 2**28, "(B6) 49*4^(l-1)*(10+2l) > 2^(2l+8) at l=10")
B2min = 1
while B2min**2 * 49**2 * 575**2 < 1300**2 * 56 * 576**2:
    B2min += 1
out["theoremB_min_integer_main_constant"] = B2min
B3min = 1
while B3min**2 * 28 < 4 * QB:
    B3min += 1
out["theoremB_min_integer_L2_constant(with log2 QB>=28)"] = B3min
# Corollary C: 9^5 QB^3 >= (40000*29)^5
check(9**5 * QB**3 >= (40000 * 29)**5, "(C1) corollary 3 q^(4/5)")
# Theorem A onset of t: t(Q1) = 160 exactly
check(512 * 160**5 == Q1 and 512 * 161**5 > Q1, "t(Q1)=160")
# Theorem B: t(QB) = 575 exactly
fB = lambda t: 49 * t * t * (10 + 2 * ell(t))
check(fB(575) == QB and fB(576) > QB, "t(QB)=575")

# ---------------- Part 2: sweeps ----------------
for t in range(3, 5001):
    l = ell(t)
    check(l <= t, "ell<=t")
    check(2**(l - 1) < t <= 2**l if t >= 2 else True, "ell def")
    # Lemma 2' simplification: t^2(2+l) + t + log2(t+1) <= 2 t^3  (use log2(t+1) <= bitlength(t+1))
    check(t * t * (2 + l) + t + (t + 1).bit_length() <= 2 * t**3, "L2' simplification")
    # log2(t!) <= t*l  (t! <= t^t <= 2^(t l))
    check(factorial(t) <= 2**(t * l) if t <= 1000 else True, "t! <= 2^(t l)")
    # ell(t+1) <= ell(t)+1
    check(ell(t + 1) <= l + 1, "ell step")
    # (P1) slack for Theorem B: t^3(10+2l) >= 48(t+1)
    check(t**3 * (10 + 2 * l) >= 48 * (t + 1), "B P1 slack")
    # Theorem A: 4t^2(2+l)+2t+2 <= 16 t^3 and 10+2l <= 8t^3
    check(4 * t * t * (2 + l) + 2 * t + 2 <= 16 * t**3 and 10 + 2 * l <= 8 * t**3, "A bounds")
    # Theorem B: 4t^2(2+l) <= 2 t^2 (10+2l)
    check(4 * (2 + l) <= 2 * (10 + 2 * l), "B C_t bound")
    if t >= 160:
        check(40 * (t // 32) >= t, "floor(t/32) >= t/40 for t >= 160")
    if t >= 575:
        check(25 * (t // 24) >= t, "floor(t/24) >= t/25 for t >= 575")
# 512 t^5 <= 2^t (file (16)) is not needed; q/8 >= log2 q + 3 at q=128: 16 >= 10
check(128 // 8 >= 7 + 3, "q/8 >= log2 q + 3 at q = 128")
# 2^q >= (C+2)^2 q^2 sweep over integer q in [64, 4096] (monotone beyond, proof in report)
for qq in range(64, 4097):
    check((3402**2) * qq * qq <= 2**qq and (8402**2) * qq * qq <= 2**qq, "transfer sweep")

# ---------------- Part 3: Lemma 2' on small cases ----------------
def hnf_key(vectors, s):
    """Canonical form (row Hermite normal form over Z) of the lattice spanned by integer vectors."""
    rows = [list(v) for v in vectors if any(v)]
    basis = []
    col = 0
    r = 0
    A = rows
    res = []
    for c in range(s):
        # gather rows with nonzero in column c among remaining
        while True:
            nz = [i for i in range(len(A)) if A[i][c] != 0]
            if len(nz) <= 1:
                break
            # Euclid step: reduce all by the one with smallest |entry|
            p = min(nz, key=lambda i: abs(A[i][c]))
            for i in nz:
                if i != p:
                    m = A[i][c] // A[p][c]
                    A[i] = [x - m * y for x, y in zip(A[i], A[p])]
        nz = [i for i in range(len(A)) if A[i][c] != 0]
        if nz:
            p = nz[0]
            v = A.pop(p)
            if v[c] < 0:
                v = [-x for x in v]
            res.append(v)
        A = [a for a in A if any(a)]
    # reduce above-pivot entries
    for i in range(len(res)):
        c = next(j for j in range(s) if res[i][j] != 0)
        for k in range(i):
            m = res[k][c] // res[i][c]
            res[k] = [x - m * y for x, y in zip(res[k], res[i])]
    return tuple(tuple(v) for v in res)

def count_lattices(s, B):
    import itertools
    box = [v for v in itertools.product(range(-B, B + 1), repeat=s) if any(v)]
    seen = {(): None}
    frontier = [()]
    while frontier:
        nf = []
        for key in frontier:
            for v in box:
                k2 = hnf_key(list(key) + [v], s)
                if k2 not in seen:
                    seen[k2] = None
                    nf.append(k2)
        frontier = nf
    return len(seen)

lemma2p = []
for (s, B) in [(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (3, 1)]:
    cnt = count_lattices(s, B)
    bound = (s + 1) * 2**s * (2 * B + 1)**(s * s) * (factorial(s) * B**s)**s
    check(cnt <= bound, f"Lemma 2' bound s={s} B={B}")
    lemma2p.append({"s": s, "B": B, "lattices": cnt, "bound": bound})
out["lemma2prime_small_cases"] = lemma2p
# known small values: lattices in Z generated by [-B,B]: {0} and dZ, d<=B
check(lemma2p[0]["lattices"] == 2 and lemma2p[1]["lattices"] == 3 and lemma2p[2]["lattices"] == 4, "Z case")

# ---------------- Part 4: sanity sweep of (P1)-(P3) ----------------
def log2_upper(q):  # q integer -> integer upper bound for log2 q
    return q.bit_length()

def P_conditions(q, h, t, a):
    """Exact check of (P1)-(P3) with q integer (N = 2^q), h a Fraction, log2 q bounded above."""
    l = ell(t)
    A = t**3 * (10 + 2 * l)
    P1 = A + a * q + t + 1 <= F(t * q, 16)
    P2 = q + 2 * t + 2 + 4 * t * t * (2 + l) + 3 + log2_upper(q) <= a * h
    P3 = h >= 3 + log2_upper(q)
    return P1 and P2 and P3

samples = []
# Theorem A: q = Q1 * m for a few m; h = ceil-free lower bound 960 q / t (Fraction)
for m in [1, 2, 7, 10**3, 10**6]:
    q = Q1 * m
    t = 160
    while 512 * (t + 1)**5 <= q:
        t += 1
    a = t // 32
    h = F(960 * q, t)
    check(P_conditions(q, h, t, a), f"sanity A q={q}")
    # and 960 q/t <= 3400 q^(4/5): (960 q/t)^5 <= 3400^5 q^4
    check((960 * q)**5 <= 3400**5 * q**4 * t**5, f"sanity A3400 q={q}")
    samples.append({"thm": "A", "q": q, "t": t, "a": a})
# Theorem B: q = QB * m; h = 200*sqrt(q*log2 q) bounded below by 200*sqrt(q*(bitlen-1))
for m in [1, 2, 3, 10, 1000, 10**6, 10**12]:
    q = QB * m
    t = 575
    while fB(t + 1) <= q:
        t += 1
    a = t // 24
    Lq = q.bit_length() - 1  # <= log2 q
    hlow = F(200 * isqrt(q * Lq * 1))  # isqrt floor: 200*floor(sqrt(qL)) <= 200 sqrt(qL)
    check(P_conditions(q, hlow, t, a), f"sanity B q={q}")
    samples.append({"thm": "B", "q": q, "t": t, "a": a, "h_lower": int(hlow)})
out["sanity_samples"] = samples

out["assertions"] = n_assert
out["cpu_seconds"] = round(time.process_time() - t_start, 3)
out["status"] = "PASS"
print(json.dumps(out, indent=1))
with open(__file__.replace(".py", ".json"), "w") as fh:
    json.dump(out, fh, indent=1)
