'use strict';
const fs=require('fs'),assert=require('assert');const cpu0=process.cpuUsage(),start=process.hrtime.bigint();
const table=JSON.parse(fs.readFileSync(process.argv[2]||'cr17d-table.json','utf8'));
const R=10n**12n,M=100000n,P=10n**40n,Cnum=4435834n,Cden=10000000n,linear=1100n;
const cd=(a,b)=>(assert(a>=0n&&b>0n),(a+b-1n)/b);
function sq(n){assert(n>=0n);if(n<2n)return n;let x=1n<<BigInt(Math.ceil(n.toString(2).length/2));for(;;){let y=(x+n/x)>>1n;if(y>=x)return x;x=y;}}
function su(n){let a=sq(n);return a*a===n?a:a+1n;}
function root(a,b){assert(a>0n);if(b<=0n)return 0n;return cd(su(a*a+4n*b*R)-a,2n);}
const U=t=>(assert(t>=0n&&t<=R),t-t*t/(2n*R));
function atan(q,terms){let lo=0n,hi=0n,p=q;for(let j=0;j<terms;j++){let d=BigInt(2*j+1)*p,f=P/d,c=cd(P,d);if(j%2){lo-=c;hi-=f;}else{lo+=f;hi+=c;}p*=q*q;}let tail=cd(P,BigInt(2*terms+1)*p);if(terms%2)lo-=tail;else hi+=tail;return[lo,hi];}
let a5=atan(5n,40),a239=atan(239n,12),piLo=16n*a5[0]-4n*a239[1],piHi=16n*a5[1]-4n*a239[0];
assert(piLo*10n**15n>3141592653589793n*P);assert(piHi*10n**15n<3141592653589794n*P);
assert(table.bin_den===10000&&table.v_den===1000000&&table.epsilon_den===4000);assert(R%(M*M)===0n);
let W=0n,sumV=0n,maxB=0n,maxLow=0n,cells=0,partialCells=0,capCells=0,fullCells=0,last=-1,details=[],fail=[];
for(let [aa,bb,vv,ee]of table.rows){assert(aa>=last&&bb>aa);last=bb;let a=BigInt(aa)*R/10000n,x=BigInt(bb)*R/10000n,v=BigInt(vv)*R/1000000n,e=BigInt(ee)*R/4000n;
let ba2=R/2n-(R-a)**2n/R,bx2=R/2n-(R-x)**2n/R;assert(ba2>0n&&x<R/2n&&v>0n);let d=sq(ba2*R)-v;assert(d>0n);let bxHi=su(bx2*R),cmin=R-x-bxHi;
assert(e>0n&&e<R/16n);assert(4n*e*R<=cmin*cmin);assert(e*R<=2n*(R/2n-x)**2n);
let D=cd(bx2*R-d*d,R),J=sq(e*M*M/R)+1n,sum=0n;
assert((J-1n)**2n*R<=e*M*M&&J*J*R>e*M*M);
for(let j=0n;j<J;j++){let p=j*R/M,q=(j+1n)*R/M,ell=R/2n-p,r=R/2n+p-x,up=R/2n+q,t=0n;let full=r*r>=2n*e*R;
if(!full){let tS=root(R/2n-q-d,e-r*r/(2n*R)+D);let t1=root(R/2n-q,U(x)+U(x+ell)-3n*R/4n+e);let t2=root(x+R/2n-q-d,U(d)+U(x-d+ell)+U(x+ell)-R+2n*e);t=tS<t1?tS:t1;if(t2<t)t=t2;}
if(full||t<d){let rr=2n*e-2n*p*p/R+D+cd(2n*d*t-t*t,R),z=root(R-x+d-2n*q-t,rr);if(t>z)z=t;let u=ell+z;if(u<up)up=u;
if(full){let z2=root(R-x-2n*q,2n*e-2n*p*p/R+cd(D,2n)),u2=ell+z2;if(u2<up)up=u2;fullCells++;}else partialCells++;
}else capCells++;
let rad=R/4n+2n*e-q-q*q/R;assert(rad>=0n);let base=sq(rad*R);if(up>base)sum+=up-base;cells++;}
let low=(4n*R-16n*e)*M*P+(R+4n*e)*M*piHi+16n*sum*P;
if(low*Cden>Cnum*16n*R*M*P)fail.push({aa,bb,coefficient:Number(low)/Number(16n*R*M*P)});
if(low>maxLow)maxLow=low;if(sum>maxB)maxB=sum;W+=(x-a)*v;sumV+=v;details.push({a:aa,b:bb,v:vv,epsilon:ee,d_scaled:d.toString(),D_scaled:D.toString(),B_num:sum.toString(),B_den:(R*M).toString()});}
const deficitNumer=(4n*P+piHi)*R*R-16n*P*W;
assert(deficitNumer*Cden<=Cnum*16n*P*R*R,'deficit branch');assert(fail.length===0,JSON.stringify(fail.slice(0,10)));
assert(9n*R+4n*sumV<=4n*linear*R);assert(7n*R+2n*maxB<=2n*linear*R);
const n0=66265061n;assert((Cnum*n0+linear*Cden)*2500n<=1109n*n0*Cden);
let cpu=process.cpuUsage(cpu0),out={status:'PASS',coefficient:'4435834/10000000',linear_error:Number(linear),onset:n0.toString(),onset_coefficient:'1109/2500',rows:details.length,cells,partialCells,capCells,fullCells,grid:M.toString(),W_num:W.toString(),W_den:(R*R).toString(),W_approx:Number(W)/Number(R*R),max_B_approx:Number(maxB)/Number(R*M),max_low_approx:Number(maxLow)/Number(16n*R*M*P),deficit_coefficient_approx:Number(deficitNumer)/Number(16n*P*R*R),sum_v_approx:Number(sumV)/Number(R),details,cost:{cpu_seconds:(cpu.user+cpu.system)/1e6,wall_seconds:Number(process.hrtime.bigint()-start)/1e9}};
fs.writeFileSync(process.argv[3]||'cr17d-certificate.json',JSON.stringify(out,null,2)+'\n');console.log(JSON.stringify({...out,details:undefined},null,2));
