# Discovery helper (not part of the proof). Scales the LP solution by (1+eta), rounds each entry UP to a
# multiple of 2^-30, and then DROPS entries whose scaled value is < 1e-12 (cutoff applied after the ceiling).
# Because of the cutoff the output is not literally an upward rounding of every entry; correctness of the
# final certificate rests only on verify.py.
import pickle,sys,math,numpy as np
L,P,delta,x1,G,D,c=pickle.load(open(sys.argv[1],'rb'))
eta=float(sys.argv[3]); nb=len(G)-1; SC=2**30
with open(sys.argv[2],'w') as f:
    f.write('%d %d %s %s\n'%(L,P,delta,x1))
    for i,d in enumerate(D):
        for b in range(nb):
            val=max(0.0,c[i*nb+b])*(1+eta)
            num=math.ceil(val*SC)
            if val<1e-12: num=0
            if num>0: f.write('%d %d %d\n'%(d,b,num))
