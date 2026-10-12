'use strict';
const V=require('./cr23c-verifier.cjs');
const cpu=process.cpuUsage(),start=process.hrtime.bigint();
function orders(a){if(!a.length)return [[]];return a.flatMap((x,i)=>orders(a.filter((_,j)=>j!==i)).map(b=>[x,...b]));}
function block(p,r,sigma,c,t){const {x}=V.labels(p),q=(p-1)/2,a=[];for(const xx of x){let z=(c*xx+t)%p;a.push((sigma[0]-1)*p+z+1);for(let j=1;j<r-1;j++){let zz=2*z%p;a.push((sigma[j]-1)*p+q+1+zz-z);z=zz;}a.push(sigma[r-1]*p-z);}return a;}
if(process.argv[2]==='large'){
 for(const p of [1009,3331,5003])for(const sigma of [[1,3,4,2],[2,1,3,4],[4,1,3,5,2]])for(const t of [0,(p-1)/2]){let a=block(p,sigma.length,sigma,1,t);V.checked(a);let count=V.exact(a);console.log(JSON.stringify({p,r:sigma.length,sigma,c:1,t,count,ratio:count/a.length/a.length}));}
}else for(const p of [101,503])for(const r of [4,5]){let best={count:-1},tested=0;for(const sigma of orders(Array.from({length:r},(_,i)=>i+1)))for(const t of [0,(p-1)/2]){let a=block(p,r,sigma,1,t);V.checked(a);let count=V.exact(a);tested++;if(count>best.count)best={count,sigma,c:1,t};}console.log(JSON.stringify({p,r,tested,best,ratio:best.count/(r*p)**2}));}
console.log(JSON.stringify({cost:{cpuMicroseconds:process.cpuUsage(cpu),elapsedSeconds:Number(process.hrtime.bigint()-start)/1e9,maxRSSKiB:process.resourceUsage().maxRSS}}));
