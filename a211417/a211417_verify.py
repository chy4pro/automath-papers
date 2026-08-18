#!/usr/bin/env python3
"""Numerical verification for notes/proofs/a211417_v1.md
(Bala's D(r) conjecture for OEIS A211417, and the companion C(k,r) family).

    a(n) = (30n)! n! / ((15n)! (10n)! (6n)!)

Theorem 3:  prod_{i<=r, gcd(i,30)=1} (30n - i)  |  D(r) * a(n)   for all n >= 0,
            with D(r) = prod_{p<=r, gcd(p,30)=1} p^E(p,r),
            E(p,r)   = sum_{k: p^k <= r} max_c #{i in L_r : i = c mod p^k}.

Theorem 4:  prod_{i<=r, gcd(i,k)=1} (k n + i)   |  C(k,r) * a(n),  k in {2,3,5}.

Runs in seconds. Requires sympy.
"""
from math import factorial, gcd, lcm
from sympy import primerange, factorint

# ---------------------------------------------------------------- Section 2
Delta = lambda j: j - j // 2 - j // 3 - j // 5
tab = [Delta(j) for j in range(30)]

assert set(tab) <= {0, 1},                       "Delta not 0/1 valued (Chebyshev)"
assert all(tab[c] == 1 for c in range(1, 30) if gcd(c, 30) == 1), "Lemma A fails"
assert all(tab[j] + tab[29 - j] == 1 for j in range(30)),         "reflection fails"
print("Delta_j (j=0..29):", tab)
print("Lemma A   : Delta_c = 1 for c in", [c for c in range(1, 30) if gcd(c, 30) == 1], "OK")
print("Property ii: Delta_j + Delta_{29-j} = 1  OK")

# Section 4 finite checks: Delta_{mc} = 0 and Delta_{mc-1} = 1, (q,m) = (2,15),(3,10),(5,6)
for q, m in [(2, 15), (3, 10), (5, 6)]:
    assert all(tab[m * c] == 0 for c in range(1, q))
    assert all(tab[m * c - 1] == 1 for c in range(1, q))
    print(f"  q={q} m={m}: Delta_[{[m*c for c in range(1,q)]}]=0, "
          f"Delta_[{[m*c-1 for c in range(1,q)]}]=1  OK")
# For 30n+i the relevant cells are all 0, i.e. the *sufficient* mechanism of Thm 3 fails.
# NOTE: this alone is NOT a proof of impossibility -- see Proposition 5 check at the end.
assert all(tab[c - 1] == 0 for c in range(1, 30) if gcd(c, 30) == 1)
print("  30n+i family: Delta_{c-1}=0 for all units c => Thm-3 mechanism inapplicable")
print("  (impossibility itself is established separately, see Proposition 5 below)\n")


def a(n):
    return factorial(30 * n) * factorial(n) // (
        factorial(15 * n) * factorial(10 * n) * factorial(6 * n))


def v_p_a(n, p):
    """v_p(a(n)) = sum_k Delta(n/p^k)   [eq. 2.1]"""
    if n == 0:
        return 0
    tot, pk = 0, p
    while pk <= 30 * n:
        tot += tab[(30 * (n % pk)) // pk]
        pk *= p
    return tot


for n in range(7):
    A = a(n)
    assert factorial(30*n)*factorial(n) == A*factorial(15*n)*factorial(10*n)*factorial(6*n)
    if n:
        for p, e in factorint(A).items():
            assert v_p_a(n, p) == e, (n, p, e, v_p_a(n, p))
print("eq.(2.1) Legendre/Delta formula cross-checked vs factorint, n <= 6  OK\n")

# ---------------------------------------------------------------- Theorem 3
L = lambda r: [i for i in range(1, r + 1) if gcd(i, 30) == 1]


def E(p, r):
    Lr, tot, pk = L(r), 0, p
    while pk <= r:
        cnt = {}
        for i in Lr:
            cnt[i % pk] = cnt.get(i % pk, 0) + 1
        tot += max(cnt.values())
        pk *= p
    return tot


def D(r):
    d = 1
    for p in primerange(2, r + 1):
        if gcd(p, 30) == 1:
            d *= p ** E(p, r)
    return d


def deficiency(n, r, p):
    """v_p(prod_i (30n-i)) - v_p(a(n))"""
    tot = 0
    for i in L(r):
        m = abs(30 * n - i)
        while m % p == 0:
            m //= p
            tot += 1
    return tot - v_p_a(n, p)


print("Theorem 3 checks")
for r in [1, 7, 11, 13, 17, 19, 23, 29, 31, 37, 49, 60, 100]:
    thy = {p: E(p, r) for p in primerange(2, r + 1) if gcd(p, 30) == 1 and E(p, r)}
    # (a) no prime p > r ever has positive deficiency  -- core of case 2 of Thm 3
    for n in range(121):
        for i in L(r):
            for p in factorint(abs(30 * n - i)):
                if p > r:
                    assert deficiency(n, r, p) <= 0, ("p>r deficiency!", r, n, i, p)
    # (b) empirical deficiency <= E(p,r)  for p <= r
    emp = {}
    for p in primerange(2, r + 1):
        if gcd(p, 30) == 1:
            w = max(deficiency(n, r, p) for n in range(401))
            if w > 0:
                emp[p] = w
            assert w <= thy.get(p, 0), ("E(p,r) violated", r, p, w, thy.get(p, 0))
    print(f"  r={r:3d} |L_r|={len(L(r)):2d}  D(r)={D(r)}")
    print(f"        thy E(p,r)={thy}")
    print(f"        emp max def={emp}   (p>r: none, n<=120)  OK")

# ------------------------- D(r) table of Sec 3.3, regenerated (v1.2, cross-review Finding 5)
print("\nSec 3.3 D(r) table (regenerated; groups of r sharing the same D(r)):")
print("| r | L_r | D(r) | factorisation |")
_rows, _prev = [], None
for r in range(1, 38):
    d = D(r)
    if _prev is not None and d == _prev[1]:
        _prev[0].append(r)
    else:
        _prev = [[r], d]
        _rows.append(_prev)
for rs, d in _rows:
    f = factorint(d)
    fac = "-" if not f else "*".join(f"{p}^{e}" if e > 1 else f"{p}" for p, e in sorted(f.items()))
    rng = f"{rs[0]}" if len(rs) == 1 else f"{rs[0]}-{rs[-1]}"
    print(f"| {rng} | {{{','.join(map(str,L(rs[0])))}}} | {d} | {fac} |")
# the exponent jumps flagged in the doc's table footnote
assert E(11, 22) == 1 and E(11, 23) == 2, "11-exponent jump at r=23"
assert E(7, 28) == 1 and E(7, 29) == 2, "7-exponent jump at r=29"
assert E(13, 36) == 1 and E(13, 37) == 2, "13-exponent jump at r=37"
assert D(23) == 81800719 == 7 * 11**2 * 13 * 17 * 19 * 23
print("  exponent jumps E(11,23)=2, E(7,29)=2, E(13,37)=2 confirmed; D(23) factorisation OK")

print("\nTheorem 3 end-to-end:  P_r(n) | D(r)*a(n)")
for r in [1, 7, 11, 13, 17, 19, 23, 29, 31, 37, 49]:
    Dr = D(r)
    for n in range(61):
        prod = 1
        for i in L(r):
            prod *= (30 * n - i)
        assert prod != 0 and (Dr * a(n)) % prod == 0, ("FAIL", r, n)
    mn = 1
    for n in range(201):
        prod = 1
        for i in L(r):
            prod *= (30 * n - i)
        mn = lcm(mn, abs(prod) // gcd(abs(prod), a(n)))
    tag = "= empirical min" if mn == Dr else f"(empirical min >= {mn}; slack {factorint(Dr//mn)})"
    print(f"  r={r:3d}: OK n=0..60   D(r)={Dr}  {tag}")

# ---------------------------------------------------------------- Theorem 4
Lk = lambda k, r: [i for i in range(1, r + 1) if gcd(i, k) == 1]


def C(k, r):
    m, Lr, d = 30 // k, Lk(k, r), 1
    for p in primerange(2, m * r + 1):
        if k % p == 0:
            continue
        e, pj = 0, p
        while pj <= m * r:
            cnt = {}
            for i in Lr:
                cnt[i % pj] = cnt.get(i % pj, 0) + 1
            e += max(cnt.values())
            pj *= p
        d *= p ** e
    return d


print("\nTheorem 4 end-to-end:  prod (k n + i) | C(k,r)*a(n)")
for k in (2, 3, 5):
    for r in (1, 2, 3, 5, 8, 12):
        Ckr = C(k, r)
        for n in range(41):
            prod = 1
            for i in Lk(k, r):
                prod *= (k * n + i)
            assert (Ckr * a(n)) % prod == 0, ("FAIL", k, r, n)
        print(f"  k={k} r={r:2d} |L|={len(Lk(k,r)):2d}: OK n=0..40   C(k,r)={Ckr}")

# --------------------------------------------- Corollary 2 (J1): log D(r) = Theta(r log r)
print("\nCorollary 2 (v1.1, J1):  log D(r) = Theta(r log r)   [the v1 claim O(r log log r) is FALSE]")
from math import log
for r in [100, 200, 400, 800, 1600, 3200]:
    # codex's lower bound on E(p,r): 1, 1+30p, 1+60p, ... all lie in L_r and in one class mod p
    for p in primerange(7, r + 1):
        if gcd(p, 30) == 1:
            assert E(p, r) >= (r - 1) // (30 * p) + 1, ("lower bound violated", r, p)
    lg = sum(E(p, r) * log(p) for p in primerange(2, r + 1) if gcd(p, 30) == 1)
    print(f"  r={r:5d}: logD={lg:10.1f}   logD/(r ln r)={lg/(r*log(r)):.4f}"
          f"   logD/(r lnln r)={lg/(r*log(log(r))):.3f}")
print("  -> logD/(r ln r) stays ~0.30 (bounded); logD/(r lnln r) keeps growing. Theta(r log r) OK")

# --------------------------------------------- Proposition 5 (J2): 30n+i is genuinely impossible
print("\nProposition 5 (v1.1, J2):  no constant D makes (30n+i) | D*a(n)")
print("  construction: p = 1 mod 30, p > i, n_e = i(p^e - 1)/30")
for i in [1, 7, 11, 13, 17, 19, 23, 29, 31]:
    for p in [31, 61, 151, 181, 211]:
        if p <= i:
            continue
        for e in [1, 2, 3]:
            n = i * (p**e - 1) // 30
            assert 30 * n + i == i * p**e
            ve, m = 0, 30 * n + i
            while m % p == 0:
                m //= p
                ve += 1
            assert ve == e, ("v_p(30n+i) != e", i, p, e, ve)
            assert v_p_a(n, p) == 0, ("v_p(a(n)) != 0", i, p, e, v_p_a(n, p))
print("  all (i,p,e) combos: v_p(30n_e+i) = e  and  v_p(a(n_e)) = 0  => p^e | D for all e  OK")

# ------------------------------- Sec 7.1 (v1.1): consistency with KitaKen1's announced witness
print("\nSec 7.1: our D(r) vs KitaKen1's announced witness  lcm(1..r)^|L_r|  (issue #4923)")
print("  claim: E(p,r) <= floor(log_p r)*|L_r|, hence our D(r) DIVIDES their witness")
for r in range(1, 81):
    Lr = len(L(r))
    for p in primerange(2, r + 1):
        if gcd(p, 30) != 1:
            continue
        k, pk = 0, p
        while pk <= r:
            k += 1
            pk *= p
        assert E(p, r) <= k * Lr, ("E(p,r) exceeds witness exponent", r, p)
print("  verified for r <= 80, all primes: no violation")
for r in [1, 7, 11, 13, 17, 23]:
    w = lcm(*range(1, r + 1)) ** len(L(r)) if r > 1 else 1
    d = D(r)
    assert w % d == 0
    print(f"    r={r:3d}: ours={d:<12d} theirs={w:<24d} ratio={w//d}")

# ------------------------------- Proposition 7 (v1.3): gcd structure behind the mixed product
print("\nProposition 7 (v1.3): gcd structure of x=2n+1, y=3n+1, z=5n+1")
print("  NOTE: the mixed product 42a/(xyz) is NOT covered by Theorem 4 -- the three forms")
print("        come from different k and are not pairwise coprime (n=1: gcd(3,6)=3).")


def vp(x, p):
    e = 0
    while x % p == 0:
        x //= p
        e += 1
    return e


for n in range(20000):
    x, y, z = 2 * n + 1, 3 * n + 1, 5 * n + 1
    assert gcd(x, y) == 1                      # 3x - 2y = 1
    assert gcd(x, z) in (1, 3)                 # 5x - 2z = 3
    assert gcd(y, z) in (1, 2)                 # 5y - 3z = 2
    assert (x % 3 == 0) == (z % 3 == 0)
    if x % 3 == 0:
        assert min(vp(x, 3), vp(z, 3)) == 1
    assert (y % 2 == 0) == (z % 2 == 0)
    if y % 2 == 0:
        assert min(vp(y, 2), vp(z, 2)) == 1
    for p in (5, 7, 11, 13, 17, 19, 23, 29, 31):
        assert sum(1 for w in (x, y, z) if w % p == 0) <= 1
assert gcd(3, 6) == 3, "the n=1 non-coprimality witness"
print("  n<20000: gcd(x,y)=1, gcd(x,z)|3, gcd(y,z)|2; shared p in {2,3} only;")
print("           when shared, min v_p = 1  => Prop 7's valuation count is exact  OK")

print("\nBala's four explicit r=1 instances, n < 400:")
for n in range(400):
    assert (7 * a(n)) % (2 * n + 1) == 0
    assert a(n) % (3 * n + 1) == 0
    assert a(n) % (5 * n + 1) == 0
    assert (42 * a(n)) % ((2 * n + 1) * (3 * n + 1) * (5 * n + 1)) == 0
    if n:
        assert a(n) % (30 * n - 1) == 0
print("  7a/(2n+1), a/(3n+1), a/(5n+1), 42a/prod, a/(30n-1)   OK")
print("\nALL CHECKS PASSED")
