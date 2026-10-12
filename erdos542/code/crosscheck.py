# Independent cross-check: build z_m = c_{gcd(m,L)}(m/n)/m for concrete n and test every dual
# constraint a*sum_k z_{ka} >= 1 directly. Exact integer enclosures with denominator Q = 2^48:
# a*z_{ka} = c/k is enclosed in [floor(C 2^18/k), ceil(C 2^18/k)] / Q.
# Usage: python3 crosscheck.py cert_main.txt n1 n2 ...
import sys
from fractions import Fraction as Fr
from math import gcd
lines = open(sys.argv[1]).read().split('\n')
L, P, delta, x1 = lines[0].split(); L = int(L); P = int(P); delta = Fr(delta)
G = sorted({Fr(p, j) for p in range(1, P + 1) for j in range(p, int(p / delta) + 1) if Fr(p, j) >= delta})
C = {}
for ln in lines[1:]:
    if ln.strip():
        e, b, num = map(int, ln.split()); C[(e, b)] = num
QS = 48; Q = 1 << QS
Vcap = Fr(10087578638, 10 ** 10); Ecap = Fr(875686331624, 10 ** 10)   # theorem constants
def dec(q, d=15, up=False):
    s = 10 ** d; v = q.numerator * s
    v = -((-v) // q.denominator) if up else v // q.denominator
    return '%d.%0*d' % (v // s, d, v % s)
def Cval(e, t):                          # exact rational bin lookup, right-closed bins
    for b in range(len(G) - 1):
        if G[b] < t <= G[b + 1]: return C.get((e, b), 0)
    return 0
allok = True
for n in map(int, sys.argv[2:]):
    Cm = [0] + [Cval(gcd(m, L), Fr(m, n)) for m in range(1, n + 1)]
    worst = None
    for a in range(1, n + 1):
        lo = sum((Cm[k * a] << (QS - 30)) // k for k in range(1, n // a + 1))
        worst = lo if worst is None else min(worst, lo)
    mass_hi = sum(-((-(Cm[m] << (QS - 30))) // m) for m in range(1, n + 1))
    feas = worst >= Q; massok = Fr(mass_hi, Q) <= Vcap + Ecap / n
    allok &= feas and massok
    print(n, 'min_a a*sum_k z_ka >=', dec(Fr(worst, Q)), ' total <=', dec(Fr(mass_hi, Q), up=True),
          ' theorem bound 1.0087578638+87.5686331624/n =', dec(Vcap + Ecap / n, up=True), ' feasible', feas, 'mass<=bound', massok)
print('CROSSCHECK', 'OK' if allok else 'FAIL')
