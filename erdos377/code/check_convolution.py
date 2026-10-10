#!/usr/bin/env python3
"""Independently verify the packed polynomial calculation on small meshes."""
from density_intervals import coefficients,powers
checked=0
for s in [2,3,4,5]:
    for M in [8,16,31]:
        for a in coefficients(s,M,12)[:2]:
            packed=powers(a,M,4)
            p=[1]
            for k in range(1,5):
                q=[0]*(len(p)+len(a)-1)
                for i,x in enumerate(p):
                    for j,y in enumerate(a):
                        q[i+j]+=x*y
                p=q
                assert packed[k-1]==(sum(p[:M+1]),sum(p[:M+k+1]))
                checked+=1
print(f'{checked} packed polynomial powers agree with independent nested-loop convolutions.')
