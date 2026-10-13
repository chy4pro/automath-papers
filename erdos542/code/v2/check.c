// Rigorous incremental check of F(N,g) >= 1 for 1<=N<=N1, all g|L.
// F(N,g) = sum_{k<=N} c_{floor(N/k), g*gcd(k,L/g)} / k,  c_{j,d} = C[j][d]/Q (integers), c_0 = c_{T0} = 0.
// Increment: F(N)-F(N-1) = sum_{j|N, j<=T0} (c_{j,e} - c_{j-1,e}) * j/N, e = g*gcd(N/j, L/g).
// We keep lower (floor) and upper (ceil) sums of Q*2^K*F in __int128.
// Input (stdin): L T0 Q N1 ; ndiv ; divisors ; then for j=1..T0-1, for each divisor d: C[j][d].
#include <stdio.h>
#include <stdlib.h>
typedef __int128 i128;
static long gcdl(long a,long b){while(b){long t=a%b;a=b;b=t;}return a;}
static i128 fdiv(i128 a, i128 b){ i128 q=a/b; if((a%b!=0)&&((a<0)!=(b<0))) q--; return q;}
static i128 cdiv(i128 a, i128 b){ return -fdiv(-a,b);}
static void pr(i128 x, char*buf){ char t[64]; int n=0; int neg=x<0; if(neg)x=-x; do{t[n++]='0'+(int)(x%10); x/=10;}while(x); int p=0; if(neg)buf[p++]='-'; while(n) buf[p++]=t[--n]; buf[p]=0;}
int main(){
  long L,T0,Q,N1; int nd; if(scanf("%ld %ld %ld %ld",&L,&T0,&Q,&N1)!=4) return 1;
  scanf("%d",&nd); long *D=malloc(nd*sizeof(long)); for(int i=0;i<nd;i++) scanf("%ld",&D[i]);
  int didx[100000]; for(long i=0;i<=L;i++) didx[i]=-1; for(int i=0;i<nd;i++) didx[D[i]]=i;
  long *C=calloc((T0+1)*nd,sizeof(long)); // C[j*nd+i], j=0..T0
  for(long j=1;j<T0;j++) for(int i=0;i<nd;i++) scanf("%ld",&C[j*nd+i]);
  const int K=64; i128 S=((i128)1)<<K; i128 target=(i128)Q*S;
  i128 *lo=calloc(nd,sizeof(i128)), *hi=calloc(nd,sizeof(i128));
  long nviol=0, namb=0; i128 *minm=malloc(nd*sizeof(i128)); long *argm=malloc(nd*sizeof(long));
  i128 big=((i128)1)<<120; for(int i=0;i<nd;i++){minm[i]=big; argm[i]=-1;}
  long N0 = 1; // report min margin over all N
  for(long N=1;N<=N1;N++){
    for(long j=1;j<=T0 && j<=N;j++){ if(N%j) continue; long k=N/j;
      for(int gi=0;gi<nd;gi++){ long g=D[gi]; long e=g*gcdl(k,L/g); int ei=didx[e];
        long dC=C[j*nd+ei]-C[(j-1)*nd+ei]; if(!dC) continue;
        i128 num=(i128)dC*j*S; lo[gi]+=fdiv(num,N); hi[gi]+=cdiv(num,N);
      }
    }
    for(int gi=0;gi<nd;gi++){
      i128 m=lo[gi]-target;
      if(m<minm[gi]){minm[gi]=m;argm[gi]=N;}
      if(lo[gi]<target){
        if(hi[gi]<target){ if(nviol<400){ printf("VIOL N=%ld g=%ld F~%.12f\n",N,D[gi],(double)lo[gi]/(double)target);} nviol++; }
        else { if(namb<50) printf("AMB N=%ld g=%ld\n",N,D[gi]); namb++; }
      }
    }
  }
  char buf[80];
  printf("DONE N1=%ld nviol=%ld namb=%ld\n",N1,nviol,namb);
  for(int gi=0;gi<nd;gi++){ printf("g=%ld minmargin(Q*2^K units)/target=%.3e at N=%ld\n",D[gi],(double)minm[gi]/(double)target,argm[gi]); }
  return 0;
}
