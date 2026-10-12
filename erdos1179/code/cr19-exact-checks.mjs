// Exact checks. No libraries, external data, or solvers.
// Run: UV_THREADPOOL_SIZE=1 node --single-threaded cr19-exact-checks.mjs
import fs from 'node:fs';
const begin = process.hrtime.bigint();
const cpuBegin = process.cpuUsage();
let assertions = 0;
function check(ok, msg) { assertions++; if (!ok) throw Error(msg); }
function primeDivisors(n) { const a=[]; for(let p=2;p<=n;p++) if(n%p===0){a.push(p);while(n%p===0)n/=p;} return a; }
function rankMod(rows, cols, p) {
  const a=rows.map(r=>r.map(x=>((x%p)+p)%p)); let r=0;
  for(let c=0;c<cols && r<a.length;c++) {
    let z=r; while(z<a.length && a[z][c]===0)z++; if(z===a.length)continue;
    [a[r],a[z]]=[a[z],a[r]]; let inv=1;while((inv*a[r][c])%p!==1)inv++;
    for(let j=c;j<cols;j++)a[r][j]=(a[r][j]*inv)%p;
    for(let i=0;i<a.length;i++)if(i!==r){const m=a[i][c];for(let j=c;j<cols;j++)a[i][j]=(a[i][j]-m*a[r][j]+p*p)%p;}
    r++;
  } return r;
}
function tuples(n,s,cb,nonzero=false) {
  const a=Array(s).fill(0); function rec(i){if(i===s){cb(a);return;}for(let x=nonzero?1:0;x<n;x++){a[i]=x;rec(i+1);}}rec(0);
}
function makeGroup(mods) {
  const n=mods.reduce((a,b)=>a*b,1),coords=[];
  for(let x=0;x<n;x++){let v=x;coords.push(mods.map(m=>{const d=v%m;v=Math.floor(v/m);return d;}));}
  function encode(a){let ans=0,w=1;for(let i=0;i<mods.length;i++){ans+=w*a[i];w*=mods[i];}return ans;}
  const add=Array.from({length:n},(_,x)=>Array.from({length:n},(_,y)=>encode(mods.map((m,i)=>(coords[x][i]+coords[y][i])%m))));
  const neg=coords.map(a=>encode(a.map((x,i)=>(mods[i]-x)%mods[i])));
  return {n,add,neg,mods};
}
function relations(G,a) {
  const s=a.length, sums=Array(1<<s).fill(0), rows=[];let key=0,count=0;
  for(let mask=0;mask<(1<<s);mask++) {
    if(mask){const bit=mask&-mask,j=31-Math.clz32(bit);sums[mask]=G.add[sums[mask^bit]][a[j]];}
    if(sums[mask]===0){key|=1<<mask;count++;rows.push(Array.from({length:s},(_,i)=>(mask>>i)&1));}
  }return {key,count,rows,total:sums[(1<<s)-1]};
}
const specs=[[2],[3],[4],[5],[6],[7],[8],[9],[10],[12],[2,2],[2,2,2],[3,3],[2,4],[2,6]];
const results=[];
for(const mods of specs){
  const G=makeGroup(mods),n=G.n,ps=primeDivisors(n);let tupleCount=0,patternCount=0,momentIdentities=0;
  const histograms=new Map();
  for(const s of [2,4]){
    const patterns=new Map(),hist=new Map(),principalHist=new Map();
    tuples(n,s,a=>{
      const z=relations(G,a);tupleCount++;
      if(!patterns.has(z.key)){
        const r=Math.max(...ps.map(p=>s-rankMod(z.rows,s,p)));
        check(z.count<=2**(s-r),`${mods}: cube bound`);
        patterns.set(z.key,{count:0,r});
      }
      patterns.get(z.key).count++;
      if(a.every(x=>x!==0)){
        hist.set(z.count,(hist.get(z.count)||0n)+1n);
        if(z.total===0)principalHist.set(z.count,(principalHist.get(z.count)||0n)+1n);
      }
    });
    for(const v of patterns.values())check(BigInt(v.count)<=BigInt(n)**BigInt(v.r),`${mods}: tuple-count bound`);
    patternCount+=patterns.size;histograms.set(s,{hist,principalHist});
  }
  for(let chi=0;chi<n;chi++){
    let order=1,x=chi;while(x!==0){x=G.add[x][chi];order++;}
    const r=relations(G,[chi,chi,G.neg[chi],G.neg[chi]]).count;
    check(r===(order===1?16:order===2?8:6),`${mods}: fourth moment, order ${order}`);
  }
  for(let k=0;k<=3;k++){
    const lhs0=new Map([[2,0n],[4,0n]]),lhsAll=new Map([[2,0n],[4,0n]]);
    tuples(n,k,a=>{
      let R=Array(n).fill(0);R[0]=1;
      for(const x of a){const next=R.slice();for(let y=0;y<n;y++)next[G.add[y][x]]+=R[y];R=next;}
      const ds=R.map(v=>BigInt(n*v-2**k));
      for(const s of [2,4]){lhs0.set(s,lhs0.get(s)+ds[0]**BigInt(s));lhsAll.set(s,lhsAll.get(s)+ds.reduce((acc,d)=>acc+d**BigInt(s),0n));}
    });
    for(const s of [2,4]){
      const {hist,principalHist}=histograms.get(s);
      const sum=h=>[...h].reduce((acc,[r,c])=>acc+c*BigInt(r)**BigInt(k),0n);
      check(lhs0.get(s)===BigInt(n)**BigInt(k)*sum(hist),`${mods}: point moment k=${k},s=${s}`);
      check(lhsAll.get(s)===BigInt(n)**BigInt(k+1)*sum(principalHist),`${mods}: spatial moment k=${k},s=${s}`);
      momentIdentities+=2;
    }
  }
  results.push({group:mods.map(m=>`C${m}`).join(' x '),order:n,tuplesEnumerated:tupleCount,relationPatterns:patternCount,momentIdentities});
}
// Exact starting values used in the analytic induction and spectral estimate.
check(3n**8n<2n**13n,'spectral strict inequality');
check(512n*64n**5n<=2n**64n,'induction base');
check(9n**5n<2n*8n**5n,'induction ratio');
for(let t=64;t<=2048;t++){
  check(512n*BigInt(t)**5n<=2n**BigInt(t),`induction finite check ${t}`);
  if(t>=500)check(Math.floor(t/32)*40>=t,`rank threshold ${t}`);
}
const cpu=process.cpuUsage(cpuBegin);
const output={status:'PASS',arithmetic:'Integer group operations and modular elimination; BigInt for all moment identities and large inequalities. No floating-point acceptance tests.',results,assertions,cpuSeconds:(cpu.user+cpu.system)/1e6,wallSeconds:Number(process.hrtime.bigint()-begin)/1e9,computeThreads:1};
const path='cr19-exact-checks.json';fs.writeFileSync(path,JSON.stringify(output,null,2)+'\n');console.log(JSON.stringify(output,null,2));
