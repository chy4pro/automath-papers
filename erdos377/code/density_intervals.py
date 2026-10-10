#!/usr/bin/env python3
"""Certified inclusion-exclusion integrals; Python standard library only.

All arithmetic supporting an enclosure uses integers or Fraction. No floating
quadrature, FFT, or assumed rounding behavior is used. Polynomial convolution
is exact Kronecker substitution (packed positive integer coefficients).
"""
from fractions import Fraction as F
from math import factorial
import argparse

Q_BITS = 56
Q = 1 << Q_BITS

def log_interval(x):
    assert 1 <= x <= F(3, 2)
    z = (x-1)/(x+1)
    z2=z*z
    term=z
    acc=F(0)
    j=0
    while True:
        acc += 2*term/(2*j+1)
        j += 1
        term *= z2
        tail = 2*term/((2*j+1)*(1-z2))
        if tail < F(1,Q*(1<<20)):
            return acc,acc+tail

def floor(x): return x.numerator//x.denominator
def ceil(x): return -((-x.numerator)//x.denominator)

def coefficients(s,M,R):
    lo=[0]*(M+1)
    hi=[0]*(M+1)
    alpha=F(1,s)
    segments=0
    for r in range(s,R):
        left,right=F(1,r+1),F(1,r)
        imin=max(1,floor(left*M/alpha)+1)
        imax=min(M,ceil(right*M/alpha))
        for i in range(imin,imax+1):
            a=max(left,alpha*F(i-1,M))
            b=min(right,alpha*F(i,M))
            if a>=b: continue
            l,u=log_interval(b/a)
            lo[i]+=floor(Q*l/(1<<r))
            hi[i]+=ceil(Q*u/(1<<r))
            segments+=1
    assert sum(hi)<Q
    return lo,hi,segments

def powers(a,M,K):
    width=(Q_BITS*K+8)//8
    B=8*width
    base=(1<<B)-1
    packed=int.from_bytes(b''.join(x.to_bytes(width,'little') for x in a),'little')
    mask=(1<<(B*(M+K+1)))-1
    power=1
    out=[]
    for k in range(1,K+1):
        power=(power*packed)&mask
        def prefix(j):
            # Sum of base-2^B digits, exact since total < Q^K < 2^B-1.
            return (power&((1<<(B*(j+1)))-1))%base
        out.append((prefix(M),prefix(M+k)))
    return out

def decimal_bounds(l,u,places=12):
    T=10**places
    a,b=floor(l*T),ceil(u*T)
    def fmt(x): return f'{x//T}.{x%T:0{places}d}'
    return '['+fmt(a)+', '+fmt(b)+']'

def calculate(s,M,R,K):
    lo,hi,segments=coefficients(s,M,R)
    pl=powers(lo,M,K)
    ph=powers(hi,M,K)
    dl=du=F(1)
    for k in range(1,K+1):
        l=F(pl[k-1][0],Q**k*factorial(k))
        u=F(ph[k-1][1],Q**k*factorial(k))
        if k%2: dl-=u;du-=l
        else: dl+=l;du+=u
    A=F(1,2**(s-1)*s)
    tau=F(1,2**(R-1)*R)
    tail=A**(K+1)/factorial(K+1)/(1-A/F(K+2))
    err=2*tau+tail
    dl-=err;du+=err
    nl,nu=1-du,1-dl
    print(f'alpha=1/{s} M={M} R={R} K={K} log_segments={segments}',flush=True)
    print('  divisor_density     '+decimal_bounds(dl,du),flush=True)
    print('  nondivisor_density  '+decimal_bounds(nl,nu),flush=True)
    print('  width_upper         '+decimal_bounds(F(0),du-dl),flush=True)
    print('  analytic_tail_upper '+decimal_bounds(F(0),err,20),flush=True)
    return (nl,nu)

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--mesh',type=int,default=8192)
    ap.add_argument('--levels',type=int,default=64)
    ap.add_argument('--terms',type=int,default=8)
    ap.add_argument('--bits',type=int,default=56)
    ap.add_argument('--s',type=int,nargs='+',default=[2,3,4,5])
    args=ap.parse_args()
    assert args.mesh>=1 and args.terms>=1 and args.bits>=8
    assert min(args.s)>=2 and args.levels>max(args.s)
    Q_BITS=args.bits
    Q=1<<Q_BITS
    for s in args.s:
        calculate(s,args.mesh,args.levels,args.terms)
