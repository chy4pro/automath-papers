# Rigorous tail bound and total for an integer-cell certificate (exact integers/rationals), fast version of tail.py.
import sys, json, numpy as np
from fractions import Fraction as Fr
from math import gcd
def ln_bounds(p,q,I=40):
    y=Fr(p-q,p+q); s=Fr(0); t=y
    for i in range(I):
        s+=t/(2*i+1); t*=y*y
    return 2*s, 2*s+2*t/((2*I+1)*(1-y*y))
def phi(m): return sum(1 for x in range(1,m+1) if gcd(x,m)==1)
def analyze(fn):
    d=json.load(open(fn)); L=d["L"];T0=d["T0"];Q=d["Q"];D=d["D"];C=d["C"]
    di={dd:i for i,dd in enumerate(D)}
    CI=lambda j,dd: C[j-1][di[dd]] if 1<=j<T0 else 0     # integer numerators
    lnl={};lnu={}
    for j in range(1,T0): lnl[j],lnu[j]=ln_bounds(j+1,j)
    ph={dd:phi(L//dd) for dd in D}
    tau_u=sum(Fr(CI(j,dd)*ph[dd],Q*L)*lnu[j] for j in range(1,T0) for dd in D)
    Kc=sum(Fr((j+1)*ph[dd]*CI(j,dd),Q) for j in range(1,T0) for dd in D)
    out={"L":L,"T0":T0,"tau_upper":float(tau_u),"K_c":float(Kc),"K_c_exact":str(Kc),"tau_upper_exact":str(tau_u)}
    rows=[]; worstN=0
    rr=np.arange(1,L+1)
    M=np.array([[2*((x0-r)%L)-L for r in range(1,L+1)] for x0 in range(L)],dtype=np.int64)
    for g in D:
        Lg=L//g; e=[g*gcd(int(r),Lg) for r in rr]
        Finf=sum(Fr(sum(CI(j,ee) for ee in e),Q*L)*lnl[j] for j in range(1,T0))
        Psi=Fr(0)
        for j in range(1,T0+1):
            dQ=np.array([CI(j-1,ee)-CI(j,ee) for ee in e],dtype=np.int64)
            if not dQ.any(): continue
            H=M@dQ; s2=2*int(dQ.sum())
            m=max(int(np.abs(H).max()), int(np.abs(H+s2).max()))
            Psi+=Fr(j*m,2*L*Q)
        R=sum(Fr(L*(j+1)**2*sum(CI(j,ee) for ee in e),6*Q) for j in range(1,T0))
        marg=Finf-1
        N1=int(Psi/marg)+1
        while marg - Psi/N1 - R/(N1*N1) < 0: N1=int(N1*1.01)+1
        worstN=max(worstN,N1)
        rows.append({"g":g,"Finf_lower":float(Finf),"Psi":float(Psi),"R":float(R),"N_tail":N1})
    out["g"]=rows; out["N_tail_max"]=worstN
    return out
if __name__=="__main__":
    o=analyze(sys.argv[1])
    if len(sys.argv)>2: json.dump(o,open(sys.argv[2],"w"),indent=1)
    print("L",o["L"],"tau_upper",o["tau_upper"],"K_c",o["K_c"],"N_tail_max",o["N_tail_max"])
    for r in o["g"]: print(r)
