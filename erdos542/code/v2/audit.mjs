// Independent exact checks for the three supplied certificates. Node.js standard library only.
// Run: node audit.mjs [finite-limit, default 100000] > audit-output.json
import fs from 'node:fs';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
const started=process.hrtime.bigint(), cpu0=process.cpuUsage();
const base=path.dirname(fileURLToPath(import.meta.url));
const assert=(x,m)=>{if(!x)throw Error(m);};
const abs=x=>x<0n?-x:x;
function gcd(a,b){while(b)[a,b]=[b,a%b];return abs(a);}
function gn(a,b){while(b)[a,b]=[b,a%b];return a;}
class R{
 constructor(n,d=1n){n=BigInt(n);d=BigInt(d);assert(d!==0n,'zero denominator');if(d<0n){n=-n;d=-d;}const g=gcd(n,d);this.n=n/g;this.d=d/g;}
 add(v){v=rat(v);return new R(this.n*v.d+v.n*this.d,this.d*v.d);}
 sub(v){v=rat(v);return new R(this.n*v.d-v.n*this.d,this.d*v.d);}
 mul(v){v=rat(v);return new R(this.n*v.n,this.d*v.d);}
 div(v){v=rat(v);return new R(this.n*v.d,this.d*v.n);}
 cmp(v){v=rat(v);const x=this.n*v.d-v.n*this.d;return x<0n?-1:x>0n?1:0;}
 toString(){return this.d===1n?''+this.n:this.n+'/'+this.d;}
}
function rat(v){if(v instanceof R)return v;if(typeof v==='string'&&v.includes('/')){const [n,d]=v.split('/');return new R(n,d);}if(typeof v==='string'&&v.includes('.')){const [a,b]=v.split('.');return new R(BigInt(a+b),10n**BigInt(b.length));}return new R(v);}
function fl(n,d){let q=n/d;if(n<0n&&n%d)q--;return q;}
function ce(n,d){return -fl(-n,d);}
function dec(v,p,up=false){v=rat(v);const s=10n**BigInt(p),q=(up?ce:fl)(v.n*s,v.d);assert(q>=0n,'positive decimal expected');return q/s+'.'+String(q%s).padStart(p,'0');}
const ln=[];
for(let j=1;j<40;j++){const y=new R(1,2*j+1),y2=y.mul(y);let t=y,s=rat(0);for(let i=0;i<40;i++){s=s.add(t.div(2*i+1));t=t.mul(y2);}ln[j]=[s.mul(2),s.mul(2).add(t.mul(2).div(rat(81).mul(rat(1).sub(y2))))];}
const limit=Number(process.argv[2]||100000);assert(Number.isSafeInteger(limit)&&limit>=70483&&limit<=10000000,'limit 70483..10000000');
const params={12:{N0:5185,m:'4479665243/1000000000000',mg:'33442881402/1000000000000',pg:17,rg:5473,P:'16566037/750000',R:'1188294863/250000',K:'2091444/15625',a:'1.00447967',b:'133.853'},60:{N0:16255,m:'2711678024/1000000000000',mg:'21435519688/1000000000000',pg:26,rg:118639,P:'2254215137/60000000',R:'10493256427/100000',K:'127600737/200000',a:'1.00271168',b:'638.004'},420:{N0:70483,m:'1890528110/1000000000000',mg:'15172074849/1000000000000',pg:49,rg:5068429,P:'3518369257/52500000',R:'232154535249/50000',K:'2081454577/500000',a:'1.00189053',b:'4162.91'}};
const out={finite_limit:limit,certificates:[],comparisons:[]};
for(const L of [12,60,420]){
 const d=JSON.parse(fs.readFileSync(path.join(base,`cert_L${L}.json`),'utf8')), {D,C,Q,T0}=d,p=params[L];
 assert(d.L===L&&Q===1000000&&T0===40,'certificate parameters');
 assert(JSON.stringify(D)===JSON.stringify(Array.from({length:L},(_,i)=>i+1).filter(x=>L%x===0)),'divisors');
 assert(C.length===39&&C.every(r=>r.length===D.length&&r.every(x=>Number.isSafeInteger(x)&&x>=0)),'coefficients');
 const maxC=Math.max(...C.flat());assert(maxC<=1500031,'maximum coefficient');
 const di=new Map(D.map((x,i)=>[x,i])),ci=(j,e)=>j>=1&&j<40?C[j-1][di.get(e)]:0;
 const phi=m=>Array.from({length:m},(_,i)=>i+1).filter(x=>gn(x,m)===1).length;
 let tau=rat(0),K=rat(0);for(let j=1;j<40;j++)for(const e of D){const c=ci(j,e)*phi(L/e);tau=tau.add(ln[j][1].mul(new R(c,Q*L)));K=K.add(new R((j+1)*c,Q));}
 assert(K.cmp(p.K)===0&&K.cmp(p.b)<=0&&tau.cmp(p.a)<=0,'headline rounding');
 const rows=[];
 for(const g of D){
  const es=Array.from({length:L},(_,i)=>g*gn(i+1,L/g));let finf=rat(0),P=rat(0),RR=rat(0);
  for(let j=1;j<40;j++){const sum=es.reduce((s,e)=>s+ci(j,e),0);finf=finf.add(ln[j][0].mul(new R(sum,Q*L)));RR=RR.add(new R(BigInt(L*(j+1)**2)*BigInt(sum),6*Q));}
  for(let j=1;j<=40;j++){
   const delta=es.map(e=>BigInt(ci(j-1,e)-ci(j,e))), total=delta.reduce((s,x)=>s+x,0n);
   let H=delta.reduce((s,x,i)=>s+x*BigInt(2*((L-(i+1))%L)-L),0n),initial=H,max=0n;
   for(let x=0;x<L;x++){max=[max,abs(H),abs(H+2n*total)].reduce((a,b)=>a>b?a:b);H+=2n*total-2n*BigInt(L)*delta[x];}
   assert(H===initial,'sawtooth periodicity');P=P.add(new R(BigInt(j)*max,2*L*Q));
  }
  const margin=finf.sub(1),slack=margin.sub(P.div(p.N0)).sub(RR.div(p.N0**2));assert(slack.cmp(0)>0,'tail onset');
  if(g===1){assert(P.cmp(p.P)===0&&RR.cmp(p.R)===0&&margin.cmp(p.m)>=0,'g=1 table');}
  else assert(margin.cmp(p.mg)>=0&&P.cmp(p.pg)<=0&&RR.cmp(p.rg)<=0,'other g table');
  rows.push({g,Finf_lower_decimal:dec(finf,15),Psi:P.toString(),R:RR.toString(),onset:p.N0,slack_lower_decimal:dec(slack,18)});
 }
 // Directed incremental enclosures, with a separate direct-sum enclosure check at selected N.
 const S=1n<<64n,target=BigInt(Q)*S,lo=D.map(()=>0n),hi=D.map(()=>0n),mins=D.map(()=>null),args=D.map(()=>0);
 const E=D.map(g=>Array.from({length:L},(_,k)=>g*gn(k,L/g)));
 const nums=Array.from({length:41},(_,j)=>D.map(e=>BigInt((ci(j,e)-ci(j-1,e))*j)*S));
 const spots=new Set([1,2,5,11,40,41,997,2586]);let nviol=0,namb=0,spotpairs=0;
 for(let N=1;N<=limit;N++){
  const BN=BigInt(N);
  for(let j=1;j<=40&&j<=N;j++)if(N%j===0){const k=N/j;for(let gi=0;gi<D.length;gi++){const num=nums[j][di.get(E[gi][k%L])];if(num){lo[gi]+=fl(num,BN);hi[gi]+=ce(num,BN);}}}
  for(let gi=0;gi<D.length;gi++){
   const margin=lo[gi]-target;if(mins[gi]===null||margin<mins[gi]){mins[gi]=margin;args[gi]=N;}
   if(lo[gi]<target){if(hi[gi]<target)nviol++;else namb++;}
   if(spots.has(N)){
    let dlo=0n,dhi=0n;for(let k=1;k<=N;k++){const num=BigInt(ci(Math.floor(N/k),E[gi][k%L]))*S;dlo+=fl(num,BigInt(k));dhi+=ce(num,BigInt(k));}
    assert(dlo<=hi[gi]&&lo[gi]<=dhi&&dlo>=target,'direct enclosure crosscheck');spotpairs++;
   }
  }
 }
 assert(nviol===0&&namb===0,'finite check');
 const tableSlack=rat(p.m).mul(p.N0**2).sub(rat(p.P).mul(p.N0)).sub(p.R);
 const otherSlack=rat(p.mg).mul(p.N0**2).sub(rat(p.pg).mul(p.N0)).sub(p.rg);assert(tableSlack.cmp(0)>0&&otherSlack.cmp(0)>0,'summary table slack');
 const result={L,divisor_classes:D.length,entries:C.flat().length,nonzero:C.flat().filter(x=>x).length,maxC,tau_upper_decimal:dec(tau,15,true),K:K.toString(),K_decimal:dec(K,6,true),nviol,namb,direct_spot_pairs:spotpairs,finite_minima:D.map((g,i)=>({g,N:args[i],margin_units:''+mins[i]})),tail:rows,table_slack:tableSlack.toString(),other_table_slack:otherSlack.toString()};
 out.certificates.push(result);
 process.stderr.write(`L=${L}: ${limit*D.length} finite pairs, ${spotpairs} direct checks, ${D.length} tails: PASS\n`);
}
// All pairwise comparisons of the four published decimal bounds.
const B=[{name:'v1',a:'1.0087578638',b:'87.5686331624'},...[12,60,420].map(L=>({name:`L${L}`,a:params[L].a,b:params[L].b}))];
for(let i=0;i<B.length;i++)for(let j=i+1;j<B.length;j++){
 const old=B[i],next=B[j],slope=rat(old.a).sub(next.a),intercept=rat(next.b).sub(old.b),root=intercept.div(slope),n=fl(root.n,root.d)+1n;
 assert(slope.mul(n).cmp(intercept)>0&&slope.mul(n-1n).cmp(intercept)<=0,'crossover');
 out.comparisons.push({smaller_after:next.name,compared_with:old.name,real_crossing:root.toString(),first_strict_integer:''+n,equality_integer:root.d===1n?''+root.n:null,sign_at_previous:slope.mul(n-1n).sub(intercept).toString(),sign_at_first:slope.mul(n).sub(intercept).toString()});
}
// Chen's bound: compare n(n-58)(B(n)-B_Chen(n)) exactly.
for(const b of B){const a=rat(b.a).sub('1.0170166'),bb=rat(b.b),poly=n=>a.mul(n).mul(n-58n).add(bb.mul(n-58n)).sub(rat('14.21').mul(n));
 // Concave quadratic, initially negative; the middle interval may be nonnegative.
 let left=59n;while(poly(left).cmp(0)<0&&left<100000n)left++;
 assert(left<100000n,'Chen lower crossing');let high=left*2n;while(poly(high).cmp(0)>=0)high*=2n;
 let low=left;while(high-low>1n){const mid=(low+high)/2n;if(poly(mid).cmp(0)>=0)low=mid;else high=mid;}
 assert(poly(left).cmp(0)>0&&poly(left-1n).cmp(0)<0&&poly(low).cmp(0)>0&&poly(high).cmp(0)<0,'no boundary equality');
 out.comparisons.push({bound:b.name,compared_with:'Chen1996',strictly_smaller_intervals:[...(left>59n?[['59',''+(left-1n)]]:[]),[''+high,'infinity']],strictly_larger_interval:[''+left,''+low],boundary_polynomial_values:[left-1n,left,low,high].map(n=>({n:''+n,value:poly(n).toString()}))});
}
const cpu=process.cpuUsage(cpu0);out.cost={wall_seconds:Number(process.hrtime.bigint()-started)/1e9,cpu_seconds:(cpu.user+cpu.system)/1e6,maxRSS_KiB:process.resourceUsage().maxRSS,worker_threads:1};
console.log(JSON.stringify(out,null,2));
