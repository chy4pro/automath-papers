'use strict';const fs=require('fs'),assert=require('assert'),crypto=require('crypto');const cpu0=process.cpuUsage(),start=process.hrtime.bigint();
const bot=k=>k*(k+1)/2,top=(n,k)=>k*(2*n-k+1)/2;
let stats={permutations:0,anchors:0,categories:0,seeds:0,triple1:0,triple2:0,geometry:0,saturated:0,low_rows:0,coupled_checks:0},seed=0x17d34210;
function rng(){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return seed>>>0;}
function tent(n){let a=[];for(let i=1;i<=n;i+=2)a.push(i);for(let i=n-n%2;i>=2;i-=2)a.push(i);return a;}
function random(n){let a=Array.from({length:n},(_,i)=>i+1);for(let i=n-1;i>0;i--){let j=rng()%(i+1);[a[i],a[j]]=[a[j],a[i]];}return a;}
function check(a,full=false){let n=a.length,T=bot(n),p=[0],S=new Set();for(let v of a)p.push(p.at(-1)+v);let rows=[];for(let k=1;k<=n;k++){rows[k]=[];for(let s=0;s+k<=n;s++){let v=p[s+k]-p[s];rows[k].push(v);S.add(v);}}
function cat(k,s,t,j,l,r,eps){let d=t-s,Z=n-k-d,M=n-2*j,core=k-d,U=k+d,E=top(n,core)+top(n,U)-T;let C=0,Gc=0,Qc=0;for(let i=0;i<n;i++)if(!(l<=i&&i<l+j)&&!(r<=i&&i<r+j)){C+=a[i];Gc+=+(s<=i&&i<t+k);Qc+=+(t<=i&&i<s+k);}
let H1=bot(M-Gc)+Z*(Gc-Qc)+bot(Gc-Qc)+(Z+2*d)*Qc+bot(Qc);
let K2=bot(M-Gc)+bot(M-Qc)+bot(Z+Gc)+bot(Z+2*d+Qc)-bot(Z)-bot(Z+2*d);
assert(C>H1-E);assert(2*C>K2-E);stats.categories++;
function wing(kk,ss,tt,ll,rr,rev){let dd=tt-ss,ZZ=n-kk-dd,RR=n-kk-j;if(ll+j>tt)return;let P=0,Vmass=0;for(let i=0;i<n;i++)if(!(ll<=i&&i<ll+j)&&!(tt<=i&&i<tt+kk)){Vmass+=(rev?a[n-1-i]:a[i]);if(ss<=i&&i<tt)P++;}
let Avec=rev?p[n-ss]-p[n-ss-kk]:p[ss+kk]-p[ss],Bvec=rev?p[n-tt]-p[n-tt-kk]:p[tt+kk]-p[tt],Lvec=rev?p[n-ll]-p[n-ll-j]:p[ll+j]-p[ll];
assert(Vmass>P*P+(ZZ-RR)*P+bot(RR)-E);stats.seeds++;
assert(Avec+Bvec+Lvec<=top(n,kk-P)+top(n,kk+j+P));stats.triple1++;
assert(Avec+Bvec+2*Lvec<=top(n,dd-P)+top(n,kk-dd+j)+top(n,kk+j+P));stats.triple2++;
if(eps!==undefined&&4000*bot(ZZ)>=2*eps*n*n){let gap=rr-ll-j;assert(p[s+k]-p[t]>C);if(P<dd){assert(Gc>=gap&&Qc>=Math.max(0,gap-P));stats.geometry++;for(let d0 of [...new Set([Math.floor(dd/4),Math.floor(dd/2),Math.floor(3*dd/4),dd])])for(let t0=0;t0<d0;t0++){let B2=n*n/2-(n-kk)**2,U0=a=>n*a-a*a/2,R0=n-kk-j;let fS=t0*t0+(j-d0)*t0+R0*R0/2-B2+d0*d0;let f1=t0*t0+j*t0-U0(kk)-U0(kk+j)+3*n*n/4;let f2=t0*t0+(kk+j-d0)*t0-U0(d0)-U0(kk-d0+j)-U0(kk+j)+n*n;if(j>=kk&&(4000*fS>=eps*n*n||4000*f1>=eps*n*n||4000*f2>=2*eps*n*n)){let q0=d0-t0;assert(dd-P>=q0);let zz=gap,lower=zz*zz+(n-kk-M+q0)*zz+M*M/2-B2+q0*q0;assert(4000*lower<2*eps*n*n);stats.coupled_checks++;}}}else{assert(P===dd);assert(Gc>=Math.max(0,gap-(RR-dd))&&Qc>=Math.max(0,gap-RR));stats.saturated++;}}
}
wing(k,s,t,l,r,false);wing(k,n-t-k,n-s-k,n-r-j,n-l-j,true);
}
for(let k=1;2*k<=n;k++){let hs=[];for(let s=0;s+k<=n;s++)if(2*rows[k][s]>T)hs.push(s);if(hs.length<2)continue;let s=hs[0],t=hs.at(-1),d=t-s;assert(d<=k);assert(2*top(n,k-d)+2*top(n,k+d)>2*T);stats.anchors++;
if(full){for(let j=1;2*j<=n;j++)for(let l=0;l+2*j<=n;l++)for(let r=l+j;r+j<=n;r++)cat(k,s,t,j,l,r);}
else for(let ee of [80,100,120,140,160,180,200,220]){let Q=(1000-ee)*n*n+2000*n;for(let j=1;2*j<=n;j++){let lo=-1,hi=-1;for(let s0=0;s0+j<=n;s0++)if(4000*rows[j][s0]>Q){if(lo<0)lo=s0;hi=s0;}if(lo<0||hi-lo<j)continue;stats.low_rows++;cat(k,s,t,j,lo,hi,ee);}}
}
stats.permutations++;return S.size;}
let maxima=[];for(let n=1;n<=8;n++){let a=Array.from({length:n},(_,i)=>i+1),count=0,mx=0;function go(j){if(j===n){count++;mx=Math.max(mx,check(a,true));return;}for(let i=j;i<n;i++){[a[i],a[j]]=[a[j],a[i]];go(j+1);[a[i],a[j]]=[a[j],a[i]];}}go(0);maxima.push({n,count,max_distinct:mx});}
let extra=[];for(let n of [16,32,64,128,256,512]){extra.push({n,kind:'tent',distinct:check(tent(n))});extra.push({n,kind:'reversed_tent',distinct:check(tent(n).reverse())});for(let i=0;i<40;i++)check(random(n));}
let hill=[];for(let n of [32,64,128]){let stamps=new Int32Array(bot(n)+1),stamp=0,evals=0,best=-1,bestA;function score(a){stamp++;evals++;let ct=0;for(let i=0;i<n;i++){let z=0;for(let j=i;j<n;j++){z+=a[j];if(stamps[z]!==stamp){stamps[z]=stamp;ct++;}}}return ct;}
for(let restart=0;restart<3;restart++){let a=restart?random(n):tent(n),cur=score(a);for(let it=0;it<3000;it++){let i=rng()%n,j=rng()%n;[a[i],a[j]]=[a[j],a[i]];let z=score(a);if(z>=cur)cur=z;else[a[i],a[j]]=[a[j],a[i]];if(cur>best){best=cur;bestA=a.slice();}}}assert(check(bestA)===best);hill.push({n,evals,distinct:best,permutation:bestA});}
const cpu=process.cpuUsage(cpu0),out={status:'PASS',maxima,stats,extra,random_seed:'0x17d34210',random_objects:240,hill,cost:{cpu_seconds:(cpu.user+cpu.system)/1e6,wall_seconds:Number(process.hrtime.bigint()-start)/1e9},source_sha256:crypto.createHash('sha256').update(fs.readFileSync(__filename)).digest('hex')};fs.writeFileSync(process.argv[2]||'cr17d-small-checks.json',JSON.stringify(out,null,2)+'\n');console.log(JSON.stringify({...out,hill:hill.map(({permutation,...r})=>r)},null,2));
