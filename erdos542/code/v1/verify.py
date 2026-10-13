# Exact verifier for the certificate. Usage: python3 verify.py cert_main.txt
# Pure standard library. Only Python integers and fractions.Fraction are used for
# anything that enters the proof; no floating point anywhere (decimals are printed
# from exact rationals by integer floor/ceil division, i.e. outward).
# cert format: line 1 "L P delta x1"; further lines "eta b C" meaning c_{eta,b} = C/2^30,
# bins b = 0..nb-1 are 0-indexed, (g_b, g_{b+1}]; every (eta,b) not listed is 0.
import sys, hashlib, time
from fractions import Fraction as Fr
from math import gcd
from array import array

t0 = time.process_time()
raw = open(sys.argv[1], 'rb').read()
print('cert sha256', hashlib.sha256(raw).hexdigest())
lines = raw.decode().split('\n')
L, P, delta, x1 = lines[0].split(); L = int(L); P = int(P); delta = Fr(delta); x1 = Fr(x1)
SH = 30                                  # c = C / 2^SH
assert all(L % (p * p) for p in range(2, L + 1)), 'L must be squarefree'
D = [d for d in range(1, L + 1) if L % d == 0]
def lcm(a, b): return a * b // gcd(a, b)
G = sorted({Fr(p, j) for p in range(1, P + 1) for j in range(p, int(p / delta) + 1) if Fr(p, j) >= delta})
assert G[0] == delta and G[-1] == 1
nb = len(G) - 1
C = {d: [0] * nb for d in D}
seen = set()
for ln in lines[1:]:
    if ln.strip():
        e, b, num = map(int, ln.split())
        assert e in D and 0 <= b < nb and num >= 0 and (e, b) not in seen
        seen.add((e, b)); C[e][b] = num
print('L', L, 'P', P, 'delta', delta, 'x1', x1, 'bins', nb, 'nonzero entries', sum(1 for e in D for b in range(nb) if C[e][b]))

def dec(q, d=18, up=False):
    """decimal string of rational q >= 0 rounded down (up=False) or up (up=True) at d digits"""
    s = 10 ** d; v = q.numerator * s
    v = -((-v) // q.denominator) if up else v // q.denominator
    return '%d.%0*d' % (v // s, d, v % s)

ok = True
# ---------------- Step B: tail, exact rational log enclosures ----------------
def logbounds(y, R=30):
    # y > 1 rational; log y = 2 sum_{j>=0} s^{2j+1}/(2j+1), s=(y-1)/(y+1);
    # remainder after R terms is in [0, 2 s^{2R+1} / ((2R+1)(1-s^2))]
    s = (y - 1) / (y + 1); assert 0 < s < 1
    lo = Fr(0); t = s
    for r in range(R): lo += 2 * t / (2 * r + 1); t *= s * s
    return lo, lo + 2 * t / ((2 * R + 1) * (1 - s * s))
LB = [logbounds(G[b + 1] / G[b]) for b in range(nb)]
VE = {}
for g in D:
    Vlo = Vhi = E = Fr(0)
    for r in range(L):
        e = lcm(g, gcd(r, L))
        for b in range(nb):
            c = Fr(C[e][b], 2 ** SH)
            Vlo += c * LB[b][0] / L; Vhi += c * LB[b][1] / L; E += c / G[b]
    VE[g] = (Vlo, Vhi, E)
    slack = Vlo - x1 * E - 1
    print('gamma', g, 'V_gamma in [%s, %s]' % (dec(Vlo), dec(Vhi, up=True)), 'E_gamma =', E,
          '= [%s, %s]' % (dec(E), dec(E, up=True)), 'tail slack V_lo - x1*E - 1 >= %s' % dec(slack) if slack >= 0 else 'NEGATIVE')
    if slack < 0: ok = False; print('FAIL tail', g)

# ---------------- Step A: finite range, exact integer prefix sums ----------------
# F_gamma(v) = sum_{k <= 1/v} c_{gamma v k}(k v)/k.  With Q = 2^48 put h(k) = floor(C * 2^18 / k),
# so h/Q <= c/k < h/Q + 1/Q.  Prefix sums Pre[g][b][K] = sum_{k<=K} h_{g v k, b}(k).
QS = 48; Q = 1 << QS
Kmax = int(P / x1)                       # floor(N/p) <= P/x1 for every point
pts = sorted({Fr(p, N) for p in range(1, P + 1) for N in range(p, int(p / x1) + 1) if Fr(p, N) >= x1})
assert pts[0] == x1 and pts[-1] == 1
Pre = {}
for g in D:
    cls = [lcm(g, gcd(k, L)) for k in range(Kmax + 1)]
    Pre[g] = {}
    for b in range(nb):
        if not any(C[e][b] for e in D if lcm(g, e) == e): continue   # classes reachable from g
        arr = array('q', [0]) * (Kmax + 1); s = 0
        for k in range(1, Kmax + 1):
            s += (C[cls[k]][b] << (QS - SH)) // k; arr[k] = s       # array('q') raises on overflow
        Pre[g][b] = arr
Tall = {g: [] for g in D}
for v in pts:
    p, N = v.numerator, v.denominator
    # K_i = floor(g_i * N / p) = #{k : k v <= g_i}; exact integer division
    Kb = [(gi.numerator * N) // (gi.denominator * p) for gi in G]
    assert Kb[-1] == N // p <= Kmax and all(Kb[i] <= Kb[i + 1] for i in range(nb))
    for g in D:
        T = 0
        for b, arr in Pre[g].items(): T += arr[Kb[b + 1]] - arr[Kb[b]]
        Tall[g].append(T)
Tmin, gmin, imin = min((T, g, i) for g in D for i, T in enumerate(Tall[g]))
def Fexact(v, g):
    p, N = v.numerator, v.denominator; s = Fr(0)
    for k in range(1, N // p + 1):
        t = k * v
        if t <= delta: continue
        b = next(i for i in range(nb) if G[i] < t <= G[i + 1])
        s += Fr(C[lcm(g, gcd(k, L))][b], 2 ** SH * k)
    return s
Fm = Fexact(pts[imin], gmin)
# every (v,g) with T/Q > Fm has F >= T/Q > Fm; the others are evaluated exactly
cands = [(g, i) for g in D for i, T in enumerate(Tall[g]) if T * Fm.denominator <= Q * Fm.numerator]
exact = min((Fexact(pts[i], g), pts[i], g) for g, i in cands)
print('points', len(pts), 'constraints', 4 * len(pts))
print('min integer lower bound T/Q =', Fr(Tmin, Q), '>= %s' % dec(Fr(Tmin, Q)), 'at v =', pts[imin], 'gamma =', gmin)
print('exact-minimum candidates', len(cands), '; exact min F =', exact[0], '>= %s' % dec(exact[0]), 'at v =', exact[1], 'gamma =', exact[2])
if Tmin < Q: ok = False; print('FAIL finite range')

# ---------------- Step C: theorem constants, onsets, benchmark overlap ----------------
V1lo, V1hi, E1 = VE[1]
Vcap = Fr(10087578638, 10 ** 10); Ecap = Fr(875686331624, 10 ** 10)
print('V_1 in [%s, %s], E_1 = %s' % (dec(V1lo), dec(V1hi, up=True), E1))
ok &= V1hi <= Vcap and E1 <= Ecap
print('V_1 <= 1.0087578638 :', V1hi <= Vcap, '; E_1 <= 87.5686331624 :', E1 <= Ecap)
for B, claim in ((Fr(10170, 10000), 10625), (Fr(101, 100), 70499)):
    n0 = -((-Ecap) // (B - Vcap))          # least n with Vcap + Ecap/n <= B
    print('onset for bound', B, ':', n0, '(claimed %d)' % claim); ok &= n0 == claim
ok &= Fr(79, 100) / (47648 - 58) >= Fr(166, 10 ** 7)
print('baseline overlap 0.79/47590 - 0.0000166 =', Fr(79, 100) / 47590 - Fr(166, 10 ** 7))
print('RESULT', 'OK' if ok else 'FAIL')
if ok: print('Theorem: for every integer n >= 1, rho(n) <= V_1 + E_1/n <= 1.0087578638 + 87.5686331624/n')
print('cpu seconds %.1f' % (time.process_time() - t0))
