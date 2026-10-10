// Exact, single-process author-revision checks; Node standard library only.
// This does not rerun or replace the Python mesh-16384 certificate.
'use strict';
const fs = require('fs');
const path = require('path');
const assert = require('assert/strict');
const start = process.hrtime.bigint(), cpuStart = process.cpuUsage();
const gcd = (a,b) => { a=a<0n?-a:a; b=b<0n?-b:b; while(b) [a,b]=[b,a%b]; return a; };
class F {
  constructor(n,d=1n) { n=BigInt(n); d=BigInt(d); assert(d!==0n); if(d<0n){n=-n;d=-d;} const g=gcd(n,d); this.n=n/g;this.d=d/g; }
  add(y) {return new F(this.n*y.d+y.n*this.d,this.d*y.d);}
  sub(y) {return new F(this.n*y.d-y.n*this.d,this.d*y.d);}
  mul(y) {return new F(this.n*y.n,this.d*y.d);}
  div(y) {return new F(this.n*y.d,this.d*y.n);}
  cmp(y) {const z=this.n*y.d-y.n*this.d;return z<0n?-1:z>0n?1:0;}
  floor() {let q=this.n/this.d;return this.n<0n&&this.n%this.d!==0n?q-1n:q;}
  ceil() {return -new F(-this.n,this.d).floor();}
}
const Q=1n<<56n, one=new F(1), two=new F(2);
const min=(a,b)=>a.cmp(b)<0?a:b, max=(a,b)=>a.cmp(b)>0?a:b;
function logBounds(x) {
  assert(x.cmp(one)>=0&&x.cmp(new F(3,2))<=0);
  const z=x.sub(one).div(x.add(one)), zz=z.mul(z);
  let term=z, acc=new F(0), j=0;
  while(true) {
    acc=acc.add(two.mul(term).div(new F(2*j+1)));
    j++;term=term.mul(zz);
    const tail=two.mul(term).div(new F(2*j+1).mul(one.sub(zz)));
    if(tail.cmp(new F(1,Q*(1n<<20n)))<0)return [acc,acc.add(tail)];
  }
}
function coefficients(s,M,R) {
  const lo=Array(M+1).fill(0n),hi=Array(M+1).fill(0n);
  for(let r=s;r<R;r++) {
    for(let i=1;i<=M;i++) {
      const a=max(new F(1,r+1),new F(i-1,s*M));
      const b=min(new F(1,r),new F(i,s*M));
      if(a.cmp(b)>=0)continue;
      const [l,u]=logBounds(b.div(a));
      lo[i]+=l.mul(new F(Q,1n<<BigInt(r))).floor();
      hi[i]+=u.mul(new F(Q,1n<<BigInt(r))).ceil();
    }
  }
  assert(hi.reduce((a,b)=>a+b,0n)<Q);
  return [lo,hi];
}
function packed(a,M,K) {
  const B=BigInt(8*Math.floor((56*K+8)/8));
  const modulus=(1n<<B)-1n;
  let encoded=0n;
  for(let i=0;i<a.length;i++)encoded+=a[i]<<(B*BigInt(i));
  const mask=(1n<<(B*BigInt(M+K+1)))-1n;
  let power=1n;const out=[];
  for(let k=1;k<=K;k++) {
    power=(power*encoded)&mask;
    const prefix=j=>(power&((1n<<(B*BigInt(j+1)))-1n))%modulus;
    out.push([prefix(M),prefix(M+k)]);
  }
  return out;
}
let convolutions=0;
for(const s of [2,3,4,5])for(const M of [8,16,31]) {
  for(const a of coefficients(s,M,12)) {
    const got=packed(a,M,4);let p=[1n];
    for(let k=1;k<=4;k++) {
      const q=Array(p.length+a.length-1).fill(0n);
      for(let i=0;i<p.length;i++)for(let j=0;j<a.length;j++)q[i+j]+=p[i]*a[j];
      p=q;
      const sum=j=>p.slice(0,j+1).reduce((x,y)=>x+y,0n);
      assert.deepEqual(got[k-1],[sum(M),sum(M+k)]);convolutions++;
    }
  }
}
console.log(`${convolutions} exact packed/nested-loop comparisons passed (s=2,3,4,5; M=8,16,31; R=12; both bounds; k=1..4).`);
const primes=[2,3,5,7,11,13,17,19,23,29,31];
function vp(x,p) {p=BigInt(p);let v=0;while(x%p===0n){x/=p;v++;}return v;}
function legendre(n,p) {let v=0;for(let w=p;w<=2*n;w*=p)v+=Math.floor(2*n/w)-2*Math.floor(n/w);return v;}
function carries(n,p) {let c=0,incoming=0;while(n||incoming){const d=n%p;incoming=2*d+incoming>=p?1:0;c+=incoming;n=Math.floor(n/p);}return c;}
let B=1n, valuations=0,powersOfTwo=0;
for(let n=0;n<=4096;n++) {
  if(n>0)B=B*BigInt(2*n)*BigInt(2*n-1)/(BigInt(n)*BigInt(n));
  if(n<=512)for(const p of primes) {
    assert.equal(vp(B,p),legendre(n,p));assert.equal(vp(B,p),carries(n,p));valuations++;
  }
  if(n>0&&(n&(n-1))===0){assert.equal(vp(B,2),1);powersOfTwo++;}
}
console.log(`${valuations} exact binomial valuations matched floor sums and digit carries (n=0..512; p=${primes.join(',')}).`);
console.log(`${powersOfTwo} exact binary-power valuations equal one (n=2^h, h=0..12).`);
const ratio=new F(10,9).mul(new F(27,20)).mul(new F(27,20)).div(new F(4,3));
assert.equal(ratio.n,243n);assert.equal(ratio.d,160n);
console.log('Printed-display endpoint example checked exactly: ratio 243/160 > 1.');
function parseTable(filename) {
  const text=fs.readFileSync(path.join(__dirname,filename),'utf8');
  const records=[];
  const re=/alpha=1\/(\d+)[^\n]*\n\s+divisor_density\s+\[([\d.]+), ([\d.]+)\]\n\s+nondivisor_density\s+\[([\d.]+), ([\d.]+)\]/g;
  for(const m of text.matchAll(re))records.push({s:Number(m[1]),values:m.slice(2)});
  assert.equal(records.length,4);return records;
}
const tex=fs.readFileSync(path.join(__dirname,'..','main.tex'),'utf8');
const fine=parseTable('density_16384.txt'),coarse=parseTable('density_4096.txt');
const dec=x=>BigInt(x.replace('.',''));
let endpoints=0;
for(let i=0;i<4;i++) {
  assert.equal(fine[i].s,coarse[i].s);
  for(const x of fine[i].values){assert(tex.includes(x));endpoints++;}
  const [dl,du,nl,nu]=fine[i].values.map(dec);
  assert.equal(dl+nu,10n**12n);assert.equal(du+nl,10n**12n);
  const old=coarse[i].values.map(dec);
  assert(old[0]<=dl&&du<=old[1]&&old[2]<=nl&&nu<=old[3]);
}
assert.equal(dec(fine[0].values[3])-dec(fine[0].values[2]),707069n);
assert(2830047n>4n*707069n);
console.log(`${endpoints} mesh-16384 endpoints matched main.tex; all complement identities and all four coarse/fine containments passed exactly.`);
const stripped=tex.replace(/%[^\n]*/g,'').replace(/\\begin\{verbatim\}[\s\S]*?\\end\{verbatim\}/g,'');
const labels=[...stripped.matchAll(/\\label\{([^}]+)\}/g)].map(x=>x[1]);
assert.equal(new Set(labels).size,labels.length);
for(const x of stripped.matchAll(/\\(?:eqref|ref)\{([^}]+)\}/g))assert(labels.includes(x[1]),x[1]);
const env=[];
for(const x of stripped.matchAll(/\\(begin|end)\{([^}]+)\}/g)){
  if(x[1]==='begin')env.push(x[2]);else assert.equal(env.pop(),x[2]);
}
assert.equal(env.length,0);
let depth=0;
for(let i=0;i<stripped.length;i++){
  if(stripped[i]==='\\'&&(stripped[i+1]==='{'||stripped[i+1]==='}')){i++;continue;}
  if(stripped[i]==='{')depth++;
  if(stripped[i]==='}')depth--;
  assert(depth>=0);
}
assert.equal(depth,0);
assert.equal((stripped.match(/\$/g)||[]).length%2,0);
assert(!/(?<!\\)\b(?:quad|qquad)\b/.test(stripped));
assert(tex.includes('\\section{Related work}\n% COORDINATOR: filled from the literature check'));
console.log(`LaTeX static check passed: balanced braces/environments/dollar delimiters; ${labels.length} unique labels; all references resolved; exact Related work placeholder retained. This is not a TeX compilation.`);
const cpu=process.cpuUsage(cpuStart);
console.log(`Cost: wall ${(Number(process.hrtime.bigint()-start)/1e9).toFixed(3)} s; process CPU ${((cpu.user+cpu.system)/1e6).toFixed(3)} s. No workers, solver, network, or external dependencies.`);
