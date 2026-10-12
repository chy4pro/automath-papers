'use strict';
const fs=require('fs');
const start=process.hrtime.bigint(), cpu=process.cpuUsage();
function prime(p){if(p<2)return false;for(let d=2;d*d<=p;d++)if(p%d===0)return false;return true;}
function pow(a,b,p){let r=1;while(b){if(b%2)r=r*a%p;a=a*a%p;b=Math.floor(b/2);}return r;}
function root(p){let factors=[],v=p-1;for(let d=2;d*d<=v;d++)if(v%d===0){factors.push(d);while(v%d===0)v/=d;}if(v>1)factors.push(v);for(let g=2;g<p;g++)if(factors.every(d=>pow(g,(p-1)/d,p)!==1))return g;throw Error('root');}
function labels(p){let g=root(p),x=new Int32Array(p);x[0]=1;for(let i=1;i<p-1;i++)x[i]=x[i-1]*g%p;return {g,x};}
function permutation(p,c,t,x){const k=(p-1)/2,T=(9*p+3)/2,a=new Int32Array(3*p);for(let i=0;i<p;i++){let q=(c*x[i]+t)%p,A=q+1,C=(q+k)%p+1;a[3*i]=A;a[3*i+1]=T-A-p-C;a[3*i+2]=p+C;}return a;}
function exact(a,buf){let n=a.length,total=n*(n+1)/2;buf=buf||new Uint8Array(Math.floor(total/8)+1);buf.fill(0);let count=0;for(let i=0;i<n;i++){let s=0;for(let j=i;j<n;j++){s+=a[j];const b=s>>>3,m=1<<(s&7);if(!(buf[b]&m)){buf[b]|=m;count++;}}}return count;}
function checked(a){let seen=new Uint8Array(a.length+1);for(const v of a){if(v<1||v>a.length||seen[v])throw Error('not permutation');seen[v]=1;}}
function scan(p,cs,ts){if(!prime(p)||p<5)throw Error('prime');let {g,x}=labels(p),n=3*p,buf=new Uint8Array(Math.floor(n*(n+1)/16)+1),best={count:-1},sum=0,byT=[];for(const t of ts){let s=0,lo=Infinity,hi=-1;for(const c of cs){const a=permutation(p,c,t,x);checked(a);const count=exact(a,buf);if(count>best.count)best={count,c,t};s+=count;lo=Math.min(lo,count);hi=Math.max(hi,count);}byT.push({t,mean:s/cs.length,min:lo,max:hi});sum+=s;}return {p,g,cCount:cs.length,tCount:ts.length,best,ratio:best.count/n/n,mean:sum/(cs.length*ts.length)/n/n,byT};}
if(require.main===module){const mode=process.argv[2]||'small';if(mode==='small'){for(const p of [5,7,11,17,31,61,101]){let r=scan(p,Array.from({length:p-1},(_,i)=>i+1),Array.from({length:p},(_,i)=>i));console.log(JSON.stringify(r));}}
else if(mode==='translations'){for(const p of [251,503,1009,2003,3331]){const {g,x}=labels(p),cs=[1,2,g,p-1];const ts=[0,Math.floor(p/8),Math.floor(p/4),Math.floor(3*p/8),(p-1)/2,Math.floor(5*p/8),Math.floor(3*p/4),Math.floor(7*p/8)];console.log(JSON.stringify(scan(p,cs,ts)));}}
else if(mode==='one'){const [p,c,t,n]=process.argv.slice(3).map(Number),{g,x}=labels(p);let a=permutation(p,c,t,x);if(n>3*p)a=Int32Array.from([...a,...Array.from({length:n-3*p},(_,i)=>3*p+i+1)]);checked(a);let count=exact(a);console.log(JSON.stringify({p,g,c,t,n:a.length,count,ratio:count/a.length/a.length}));}
else throw Error('mode');
console.log(JSON.stringify({cost:{cpuMicroseconds:process.cpuUsage(cpu),elapsedSeconds:Number(process.hrtime.bigint()-start)/1e9,maxRSSKiB:process.resourceUsage().maxRSS}}));}
module.exports={prime,pow,root,labels,permutation,exact,checked,scan};
