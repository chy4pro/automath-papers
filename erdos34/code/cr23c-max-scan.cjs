'use strict';
const V=require('./cr23c-verifier.cjs');
const cpu=process.cpuUsage(),start=process.hrtime.bigint();
function allC(p,t,audit=false){
 const {g,x}=V.labels(p),a=V.permutation(p,1,t,x),n=3*p,m=n-3,z=a.slice(m),core=new Int32Array(2*m);
 core.set(a.slice(0,m));core.set(a.slice(0,m),m);
 const total=n*(n+1)/2,cnt=new Uint16Array(total+1);let distinct=0;
 function add(v){if(cnt[v]++===0)distinct++;}
 function del(v){if(cnt[v]===0)throw Error('negative');if(--cnt[v]===0)distinct--;}
 for(let i=0;i<m;i++){let s=0;for(let j=i;j<m;j++){s+=core[j];add(s);}}
 for(let i=0;i<3;i++){let s=0;for(let j=i;j<3;j++){s+=z[j];add(s);}}
 function tails(st,plus){let q=0;for(let j=0;j<3;j++){q+=z[j];let s=q;for(let i=st+m-1;i>=st;i--){s+=core[i];if(plus)add(s);else del(s);}}}
 tails(0,true);let c=1,best={count:-1},sum=0;
 for(let r=0;r<p-1;r++){
  if(audit){let expected=V.exact(V.permutation(p,c,t,x));if(expected!==distinct)throw Error(JSON.stringify({p,t,c,expected,distinct}));}
  if(distinct>best.count)best={count:distinct,c,t};sum+=distinct;
  if(r===p-2)break;
  const st=3*r;tails(st,false);
  for(let i=st;i<st+3;i++){let s=0;for(let j=i;j<st+m;j++){s+=core[j];del(s);}}
  for(let j=st+m;j<st+m+3;j++){let s=0;for(let i=j;i>=st+3;i--){s+=core[i];add(s);}}
  tails(st+3,true);c=c*g%p;
 }
 return {best,sum};
}
if(require.main===module){const ps=process.argv.slice(2).map(Number);for(const p of ps){let best={count:-1},sum=0;for(let t=0;t<p;t++){let r=allC(p,t,p<=31);if(r.best.count>best.count)best=r.best;sum+=r.sum;}console.log(JSON.stringify({p,g:V.root(p),tested:p*(p-1),best,ratio:best.count/(9*p*p),mean:sum/(p*(p-1)*9*p*p)}));}console.log(JSON.stringify({cost:{cpuMicroseconds:process.cpuUsage(cpu),elapsedSeconds:Number(process.hrtime.bigint()-start)/1e9,maxRSSKiB:process.resourceUsage().maxRSS}}));}
module.exports={allC};
