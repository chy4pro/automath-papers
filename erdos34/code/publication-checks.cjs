'use strict';
// Supplemental exact arithmetic and source-structure checks.
// The original mathematical programs and stored outputs are unmodified.
const fs = require('fs');
const path = require('path');
const assert = require('assert');
const start = process.hrtime.bigint(), cpu = process.cpuUsage();
const here = __dirname;
const read = name => JSON.parse(fs.readFileSync(path.join(here, name), 'utf8'));
const ceil = (a, b) => { assert(a >= 0n && b > 0n); return (a + b - 1n) / b; };
function sqrtFloor(v) {
  assert(v >= 0n);
  let lo = 0n, hi = 1n;
  while (hi * hi <= v) hi *= 2n;
  while (hi - lo > 1n) { const m = (lo + hi) / 2n; if (m*m <= v) lo = m; else hi = m; }
  return lo;
}
function gcd(a,b) { while (b) [a,b]=[b,a%b]; return a < 0n ? -a : a; }
const rat = (a,b=1n) => { const g=gcd(a,b); return [a/g,b/g]; };
const add = (a,b) => rat(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
const mul = (a,b) => rat(a[0]*b[0],a[1]*b[1]);
const neg = a => [-a[0],a[1]];
const le = (a,b) => a[0]*b[1] <= b[0]*a[1];
const textRat = a => a[0]+'/'+a[1];
const table=read('cr17d-table.json'), cert=read('cr17d-certificate.json');
assert.equal(table.rows.length,892); assert.equal(cert.details.length,892);
assert.equal(table.bin_den,10000); assert.equal(table.v_den,1000000); assert.equal(table.epsilon_den,4000);
const R=10n**12n, piHi=rat(3141592653589794n,10n**15n);
const B0=add(rat(1n,4n),mul(piHi,rat(1n,16n))), target=rat(4435834n,10n**7n);
let minExterior=R, W=rat(0n), sumV=rat(0n), maxB=rat(0n), maxLow=rat(0n);
for(let i=0;i<table.rows.length;i++) {
  const [a,b,v,e]=table.rows[i].map(BigInt), x=b*R/10000n;
  const rad=R*R/2n-(R-x)**2n, floor=sqrtFloor(rad), upper=floor+(floor*floor===rad?0n:1n);
  const exterior=R-x-upper; assert(exterior>0n,'exterior sign');
  if(exterior<minExterior)minExterior=exterior;
  const row=cert.details[i];
  assert.deepEqual([row.a,row.b,row.v,row.epsilon],table.rows[i]);
  const Bi=rat(BigInt(row.B_num),BigInt(row.B_den)), eps=rat(e,4000n);
  const low=add(add(B0,neg(mul(add(rat(1n),neg(mul(piHi,rat(1n,4n)))),eps))),Bi);
  assert(le(low,target),'stored row coefficient');
  assert(le(add(rat(7n,2n),mul(rat(100000n),Bi)),rat(1100n)),'row linear term');
  W=add(W,mul(rat(b-a,10000n),rat(v,1000000n))); sumV=add(sumV,rat(v,1000000n));
  if(le(maxB,Bi))maxB=Bi; if(le(maxLow,low))maxLow=low;
}
assert.equal(textRat(W),'2798309/1000000000');
assert(le(add(B0,neg(W)),target)); assert(le(add(rat(9n,4n),sumV),rat(1100n)));
const n0=66265061n;
assert(le(add(target,rat(1100n,n0)),rat(1109n,2500n)));
assert(!le(add(target,rat(1100n,n0-1n)),rat(1109n,2500n)));
const onset416=50000n*419n**8n*9000000n<31n*2n**104n;
const onset448=50000n*451n**8n*90000000n<67n*2n**112n;
const padding=3097993n*99999989n**2n>3097990n*100000000n**2n;
assert(onset416&&onset448&&padding);

// Rigorous bracket for the real positivity threshold in log_2(p).
// Fixed-point lower/upper bounds for log(2) from its positive atanh series.
const S=10n**90n, terms=120;
let logLo=0n,logHi=0n,power=3n;
for(let j=0;j<terms;j++) {
  const den=BigInt(2*j+1)*power;
  logLo+=2n*S/den; logHi+=ceil(2n*S,den); power*=9n;
}
// Tail <= 9/(4(2m+1)3^(2m+1)).
logHi+=ceil(9n*S,4n*BigInt(2*terms+1)*power);
function expBounds(yLo,yHi) {
  let tl=S,tu=S,sl=S,su=S;
  for(let k=1;k<=600;k++) {
    tl=tl*yLo/(S*BigInt(k)); tu=ceil(tu*yHi,S*BigInt(k));
    sl+=tl; su+=tu;
  }
  const next=ceil(tu*yHi,S*601n);
  assert(yHi<S*602n);
  // Subsequent ratios are <= yHi/(602S).
  su+=ceil(next*602n*S,602n*S-yHi);
  return [sl,su];
}
function positivitySign(xNum,xDen) {
  const uLo=xNum*logLo/xDen, uHi=ceil(xNum*logHi,xDen);
  const [expLo,expHi]=expBounds(uLo/4n,ceil(uHi,4n));
  const leftLo=288n*50000n*(uLo+3n*S)**8n;
  const leftHi=288n*50000n*(uHi+3n*S)**8n;
  const rightLo=803n*expLo*S**7n, rightHi=803n*expHi*S**7n;
  if(leftLo>rightHi)return 'negative';
  if(leftHi<rightLo)return 'positive';
  throw Error('threshold bracket inconclusive');
}
assert.equal(positivitySign(304219n,1000n),'negative');
assert.equal(positivitySign(304221n,1000n),'positive');

// Static source checks are not a substitute for a TeX compilation.
let tex=fs.readFileSync(path.join(here,'..','main.tex'),'utf8');
assert(!/\/work\/|\/home\/|AUT-\d|CR-|cr17|cr23|agent:\/\/|mailto:|session_id/i.test(tex));
tex=tex.replace(/(^|[^\\])%.*/gm,'$1');
let depth=0;
for(let i=0;i<tex.length;i++) {
  let back=0;for(let j=i-1;j>=0&&tex[j]==='\\';j--)back++;
  if(back%2)continue;
  if(tex[i]==='{')depth++;
  if(tex[i]==='}') { depth--; assert(depth>=0,'brace underflow'); }
}
assert.equal(depth,0,'unbalanced braces');
const env=[];
for(const m of tex.matchAll(/\\(begin|end)\{([^}]+)\}/g)) {
  if(m[1]==='begin')env.push(m[2]); else assert.equal(env.pop(),m[2],'environment mismatch');
}
assert.equal(env.length,0);
const labels=[...tex.matchAll(/\\label\{([^}]+)\}/g)].map(m=>m[1]);
assert.equal(new Set(labels).size,labels.length,'duplicate label');
for(const m of tex.matchAll(/\\(?:eqref|ref)\{([^}]+)\}/g))assert(labels.includes(m[1]),'missing reference '+m[1]);
const bib=[...tex.matchAll(/\\bibitem\{([^}]+)\}/g)].map(m=>m[1]);
for(const m of tex.matchAll(/\\cite(?:\[[^\]]*\])?\{([^}]+)\}/g))for(const key of m[1].split(','))assert(bib.includes(key),'missing citation '+key);
assert.equal([...tex.matchAll(/\\begin\{theorem\}/g)].length,3);
const timing=process.cpuUsage(cpu);
console.log(JSON.stringify({status:'PASS',upperRows:table.rows.length,positiveExteriorRows:table.rows.length,minExteriorScaled:String(minExterior),scale:String(R),W:textRat(W),sumV:textRat(sumV),maxStoredB:textRat(maxB),maxStoredRowCoefficientWithPiUpper:textRat(maxLow),upperOnsetExactMinimum:String(n0),onset416,onset448,padding,positivityThresholdLog2Bracket:['304.219','304.221'],thresholdBracketArithmetic:'directed BigInt log/exp series',latexStaticChecks:{balancedBraces:true,balancedEnvironments:true,uniqueLabels:labels.length,resolvedReferences:true,resolvedCitations:true,mainTheorems:3,privacyScan:true,compiled:false},cost:{cpuSeconds:(timing.user+timing.system)/1e6,wallSeconds:Number(process.hrtime.bigint()-start)/1e9}},null,2));
