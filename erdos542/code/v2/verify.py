# Verifier for integer-cell limit certificates.  Usage: python3 verify.py CERT.json [N1]
# Needs ./check (gcc -O2 -o check check.c) and tail2.py in the same directory.
# Proves: rho(n) <= tau_upper + K_c/n for all n >= 1, provided (a) check reports 0 violations and 0 ambiguous
# cases for all N <= N1 and g | L, and (b) tail2's N_tail_max <= N1 (Euler-Maclaurin tail covers N >= N_tail).
import sys, json, subprocess
from tail2 import analyze
from fractions import Fraction

def upward_decimal(value, places):
    value = Fraction(value)
    scale = 10**places
    units = -((-value.numerator * scale) // value.denominator)
    return f"{units // scale}.{units % scale:0{places}d}"

fn=sys.argv[1]; N1=int(sys.argv[2]) if len(sys.argv)>2 else 10**7
d=json.load(open(fn)); L,T0,Q,D,C=d["L"],d["T0"],d["Q"],d["D"],d["C"]
assert all(isinstance(x,int) and x>=0 for row in C for x in row) and len(C)==T0-1 and all(len(r)==len(D) for r in C)
assert sorted(D)==[x for x in range(1,L+1) if L%x==0]
inp=f"{L} {T0} {Q} {N1}\n{len(D)}\n"+" ".join(map(str,D))+"\n"+"\n".join(" ".join(map(str,r)) for r in C)+"\n"
out=subprocess.run(["./check"],input=inp,capture_output=True,text=True).stdout
last=[l for l in out.splitlines() if l.startswith("DONE")][0]
nviol=int(last.split("nviol=")[1].split()[0]); namb=int(last.split("namb=")[1].split()[0])
t=analyze(fn)
ok = nviol==0 and namb==0 and t["N_tail_max"]<=N1
print(f"L={L} T0={T0}: exact check N<={N1}: nviol={nviol} namb={namb}; tail valid for N>={t['N_tail_max']}")
tau_display = upward_decimal(t["tau_upper_exact"], 15)
K_display = upward_decimal(t["K_c_exact"], 6)
print(f"  tau_upper <= {tau_display} (rounded upward); K_c={t['K_c_exact']} <= {K_display}")
print(f"  VERIFIED: rho(n) <= {tau_display} + {K_display}/n for all n>=1" if ok else "  NOT VERIFIED")
