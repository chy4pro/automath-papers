'use strict';
const V=require('./cr23c-verifier.cjs');
const cpu=process.cpuUsage(),start=process.hrtime.bigint();
let permutations=0,centralGeometry=0,domainChecks=0,volumeChecks=0,maskChecks=0,restoredChecks=0;
function eq(x,y,msg){if(x!==y)throw Error(msg+': '+x+' != '+y);}
for(const p of [5,7,11,13,17,19,23,29,31]){
 const k=(p-1)/2,N=p-1,T=(9*p+3)/2,H=(5*p+3)/2,{x}=V.labels(p);
 let f4=0,f5=0;
 for(let a=1;a<=p;a++)for(let b=1;b<=p;b++)for(let c=1;c<=p;c++){const d=H-a-b-c;if(d>=1&&d<=p){f4++;if(c+d<=p)f5++;}}
 eq(48*f4,23*p**3+15*p*p+p+9,'F4 volume');eq(48*f5,(p*p-1)*(5*p-3),'F5 volume');volumeChecks+=2;
 let mp=0,mn=0,mo=0;
 for(let d=1;d<N;d++)for(let i=0;i<N;i++)for(let j=0;j<N;j++){
  const pos=i<N-d&&j<d,neg=i<N-d&&d>=3&&j>=N-d+2;
  const overlap=d<k&&((i<k-d)||(i>=k&&i<N-d))&&j<d;
  const U=i+d<N;
  const overlapMask=j<d&&U&&d<k&&(((i+d)%N<k)||(i>=k));
  eq(+overlap,+overlapMask,'overlap domain factorization');maskChecks++;
  mp+=pos;mn+=neg;mo+=overlap;
 }
 eq(6*mp,N*(N*N-1),'Mplus');eq(6*mn,(N-2)*((N-2)**2-1),'Mminus');eq(3*mo,k**3-k,'Moverlap');domainChecks+=3;
 for(let t=0;t<p;t++){
  let geom=0,b=(2*t+k)%p,l=b+1;
  const A=z=>((z+t)%p+p)%p+1,C=z=>((z+t+k)%p+p)%p+1;
  for(let X=0;X<p;X++)for(let Y=0;Y<p;Y++){
   let actual=A(Y)-A(X)===C(-X)-C(-Y)&&A(Y)>A(X);
   let u=A(X)-1,v=A(Y)-1,expected=u<v&&((u<=b&&v<=b)||(u>b&&v>b));
   eq(+actual,+expected,'central lift geometry');geom+=actual;centralGeometry++;
  }
  eq(2*geom,l*(l-1)+(p-l)*(p-l-1),'central lift volume');volumeChecks++;
  for(let c=1;c<p;c++){
   const a=V.permutation(p,c,t,x);V.checked(a);permutations++;
   let pref=[0];for(const v of a)pref.push(pref[pref.length-1]+v);
   const all=new Set();for(let i=0;i<a.length;i++)for(let j=i+1;j<=a.length;j++)all.add(pref[j]-pref[i]);
   eq(all.size,V.exact(a),'bitset count');
   let base=new Set();for(let i=0;i<pref.length;i++)for(let j=i+1;j<pref.length;j++)if(i%3===0||j%3===0)base.add(pref[j]-pref[i]);
   eq(base.size,2*p*p+3*p,'base');
   const aa=Array.from({length:p},(_,i)=>a[3*i]),cc=Array.from({length:p},(_,i)=>a[3*i+2]-p);
   const rByD=[],qByD=[];
   for(let d=1;d<N;d++){
    const ca=new Set(),cb=new Set(),rr=new Set(),qq=new Set();
    for(let i=0;i<N-d;i++){
     const da=aa[i+d]-aa[i],db=cc[i]-cc[i+d];ca.add(d*T+da);cb.add(d*T+db);
     for(const delta of [da,db]){
      const j=aa.indexOf(Math.abs(delta));const missing=delta>0?j<d:j>p-d;
      eq(+(!base.has(d*T+delta)),+missing,'missing central label');
     }
     if(d>=2&&d!==k){rr.add((d+1)*T-p-cc[i+d]-aa[i]);qq.add((d-1)*T+p+cc[i]+aa[i+d]);}
    }
    eq(ca.size,N-d,'central A injection');eq(cb.size,N-d,'central B injection');
    if(d>=2&&d!==k){eq(rr.size,N-d,'cross R injection');eq(qq.size,N-d,'cross Q injection');}
    rByD[d]=rr;qByD[d]=qq;
    for(const s of [...ca,...cb,...rr,...qq])if(!all.has(s))throw Error('candidate not interval sum');
   }
   for(let d=2;d<=p-3;d++)if(d!==k-1&&d!==k){const found=new Set();for(const value of rByD[d])if(qByD[d+1].has(value)){
    const s=value-d*T-p,v=(d+1)*T-p-value;
    eq(s+v,H,'overlap equation');
    const js=cc.indexOf(s),jv=cc.indexOf(v);
    const low=js>=0&&js<=p-2-d,high=jv>=d&&jv<=p-2;
    if(low&&high)throw Error('restoration branches intersect');
    if(low||high){if(!base.has(value)||found.has(value))throw Error('invalid restoration');found.add(value);restoredChecks++;}
   }}
  }
 }
}
const onset1L=50000n*419n**8n*9000000n,onset1R=31n*2n**104n;
const onset2L=50000n*451n**8n*90000000n,onset2R=67n*2n**112n;
const padL=3097993n*99999989n**2n,padR=3097990n*100000000n**2n;
if(!(onset1L<onset1R&&onset2L<onset2R&&padL>padR))throw Error('onset or padding');
console.log(JSON.stringify({permutations,centralGeometry,domainChecks,volumeChecks,maskChecks,restoredChecks,onset1:{left:String(onset1L),right:String(onset1R),pass:true},onset2:{left:String(onset2L),right:String(onset2R),pass:true},padding:{left:String(padL),right:String(padR),pass:true}}));
console.log(JSON.stringify({cost:{cpuMicroseconds:process.cpuUsage(cpu),elapsedSeconds:Number(process.hrtime.bigint()-start)/1e9,maxRSSKiB:process.resourceUsage().maxRSS}}));
