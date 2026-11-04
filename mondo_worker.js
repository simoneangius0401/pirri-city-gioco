
 let Q=null,QH=null;const BC=new Map();
 const hq=(x,z)=>{let u=(x-Q.x0)/Q.s,v=(z-Q.z0)/Q.s;u=u<0?0:u>Q.nx-1.001?Q.nx-1.001:u;v=v<0?0:v>Q.nz-1.001?Q.nz-1.001:v;const i=u|0,j=v|0,fu=u-i,fv=v-j,k=j*Q.nx+i;return(QH[k]*(1-fu)*(1-fv)+QH[k+1]*fu*(1-fv)+QH[k+Q.nx]*(1-fu)*fv+QH[k+Q.nx+1]*fu*fv)/10};
 const ht=(x,z)=>{let u=(x-Q.x0)/Q.s,v=(z-Q.z0)/Q.s;u=u<0?0:u>Q.nx-1.001?Q.nx-1.001:u;v=v<0?0:v>Q.nz-1.001?Q.nz-1.001:v;const i=u|0,j=v|0,fu=u-i,fv=v-j,k=j*Q.nx+i,a=QH[k]/10,b=QH[k+1]/10,c=QH[k+Q.nx]/10,d=QH[k+Q.nx+1]/10;
  return fu+fv<=1?a+(b-a)*fu+(c-a)*fv:d+(c-d)*(1-fu)+(b-d)*(1-fv)};
 const hs=n=>{const v=Math.sin(n*127.1+311.7)*43758.5453;return v-Math.floor(v)};
 const PAL=[0xf2f0ea,0xf2f0ea,0xead9b0,0xead9b0,0xe6d48c,0xe6d48c,0xe3d6b8,0xd9c7a0,0xe3a9a2,0xe9b3a4,0xe9a98c,0xe3a56a,0xd9a85a,0xc8554a,0xead9b0,0xc9c5bc,0xdcd9d2,0xb9c4a2,0xecc4b4,0xf0ece2];
 const rgb=c=>[(c>>16&255)/255,(c>>8&255)/255,(c&255)/255];
 class B{constructor(){this.p=[];this.n=[];this.u=[];this.c=[]}f(){return{p:new Float32Array(this.p),n:new Float32Array(this.n),u:new Float32Array(this.u),c:new Float32Array(this.c)}}}
 // triangolazione a orecchie (poligoni semplici, gia' in senso antiorario)
 function ear(P){const n=P.length/2,V=[];for(let i=0;i<n;i++)V.push(i);const T=[];let g=0;
  const cr=(a,b,c)=>(P[2*b]-P[2*a])*(P[2*c+1]-P[2*a+1])-(P[2*b+1]-P[2*a+1])*(P[2*c]-P[2*a]);
  const inT=(p,a,b,c)=>{const x=P[2*p],z=P[2*p+1],d1=(P[2*b]-P[2*a])*(z-P[2*a+1])-(P[2*b+1]-P[2*a+1])*(x-P[2*a]),d2=(P[2*c]-P[2*b])*(z-P[2*b+1])-(P[2*c+1]-P[2*b+1])*(x-P[2*b]),d3=(P[2*a]-P[2*c])*(z-P[2*c+1])-(P[2*a+1]-P[2*c+1])*(x-P[2*c]);return d1>=0&&d2>=0&&d3>=0};
  while(V.length>3&&g<5000){g++;let ok=false;for(let i=0;i<V.length;i++){const a=V[(i+V.length-1)%V.length],b=V[i],c=V[(i+1)%V.length];if(cr(a,b,c)<=1e-9)continue;let e=true;for(const q of V){if(q===a||q===b||q===c)continue;if(inT(q,a,b,c)){e=false;break}}if(!e)continue;T.push(a,b,c);V.splice(i,1);ok=true;break}if(!ok){for(let i=1;i<V.length-1;i++)T.push(V[0],V[i],V[i+1]);return T}}
  if(V.length==3)T.push(V[0],V[1],V[2]);return T}
 function build(d,lod){
  const ox=d.o[0],oz=d.o[1],T=500,core=d.core,M=700,out={key:d.key,lod};
  // --- terreno con la foto (salta la parte gia' coperta dalla mappa di Pirri e dalla sua cornice) ---
  if(d.g){const S=20,N=T/S+1,p=new Float32Array(N*N*3),u=new Float32Array(N*N*2),n=new Float32Array(N*N*3),I=[];
   for(let j=0;j<N;j++)for(let i=0;i<N;i++){const x=ox+i*S,z=oz+j*S,k=j*N+i;p[3*k]=x;p[3*k+1]=hq(x,z);p[3*k+2]=z;u[2*k]=i/(N-1);u[2*k+1]=j/(N-1);
    const dx=hq(x+S,z)-hq(x-S,z),dz=hq(x,z+S)-hq(x,z-S),l=Math.hypot(dx,2*S,dz);n[3*k]=-dx/l;n[3*k+1]=2*S/l;n[3*k+2]=-dz/l}
   for(let j=0;j<N-1;j++)for(let i=0;i<N-1;i++){const ax0=ox+i*S,az0=oz+j*S;if(ax0>=core[0]&&ax0+S<=core[2]&&az0>=core[1]&&az0+S<=core[3])continue;const k=j*N+i;I.push(k,k+N,k+1,k+1,k+N,k+N+1)}
   out.ground={p,u,n,i:new Uint32Array(I)}}
  // --- acqua (mare, stagni, saline): superficie piana a quota 0 sulle celle bagnate ---
  if(d.wm){const S=20,N=T/S+1,P=[],wet=(i,j)=>i>=0&&j>=0&&i<N&&j<N&&((d.wm[j]>>i)&1);
   for(let j=0;j<N-1;j++)for(let i=0;i<N-1;i++){if(!(wet(i,j)||wet(i+1,j)||wet(i,j+1)||wet(i+1,j+1)))continue;const x0=ox+i*S,z0=oz+j*S;if(x0>=core[0]&&x0+S<=core[2]&&z0>=core[1]&&z0+S<=core[3])continue;P.push(x0,0,z0,x0,0,z0+S,x0+S,0,z0,x0+S,0,z0,x0,0,z0+S,x0+S,0,z0+S)}
   if(P.length){const p=new Float32Array(P),n=new Float32Array(P.length);for(let q=1;q<n.length;q+=3)n[q]=1;out.water={p,n,u:new Float32Array(P.length/3*2),c:new Float32Array(0)}}}
  // --- strade: nastri che seguono il terreno, strisce di mezzeria e marciapiedi ---
  const R=new B(),SEG=new Map(),sk=(x,z)=>Math.floor(x/12)+','+Math.floor(z/12);
  const COL={0:0x45474b,1:0x45474b,2:0x3e4044,3:0x3e4044,4:0x404246,5:0x404246,6:0x46484b,7:0x48494c,9:0x55565a,10:0xb4ada0,11:0x9a5a4a,12:0x9a8868,13:0xbdb5a5,14:0xa9a397,15:0x9f9070,20:0x6d655b};
  const RW=d.r.map(r=>{const c=r[0],w=r[1]/10,fl=r[2],br=fl&1,st=br?3:2,P=[];for(let k=4;k+1<r.length;k+=st)P.push([ox+r[k]/10,oz+r[k+1]/10,br?r[k+2]/10:null]);return{c,w,br,P}});
  for(const r of RW){if(r.c>=10&&r.c!=13)continue;for(let k=0;k<r.P.length-1;k++){const a=r.P[k],b=r.P[k+1],L=Math.hypot(b[0]-a[0],b[1]-a[1]),n=Math.max(1,Math.ceil(L/12));for(let s=0;s<=n;s++){const x=a[0]+(b[0]-a[0])*s/n,z=a[1]+(b[1]-a[1])*s/n,key=sk(x,z);let L2=SEG.get(key);if(!L2)SEG.set(key,L2=[]);L2.push([a[0],a[1],b[0],b[1],r.w/2,r])}}}
  const trim=(P,d)=>{let L=0;for(let k=1;k<P.length;k++)L+=Math.hypot(P[k][0]-P[k-1][0],P[k][1]-P[k-1][1]);if(L<2*d+2)return null;const cut=(Q,dd)=>{const o=[];let acc=0;for(let k=1;k<Q.length;k++){const a=Q[k-1],b=Q[k],l=Math.hypot(b[0]-a[0],b[1]-a[1]);if(acc+l<dd){acc+=l;continue}const f=(dd-acc)/(l||1);o.push([a[0]+(b[0]-a[0])*f,a[1]+(b[1]-a[1])*f,a[2]!=null?a[2]+(b[2]-a[2])*f:null]);for(let q=k;q<Q.length;q++)o.push(Q[q]);return o}return Q};return cut(cut(P,d).reverse(),d).reverse()};
  const onOther=(x,z,me)=>{const L2=SEG.get(sk(x,z));if(!L2)return false;for(const s of L2){if(s[5]===me)continue;const dx=s[2]-s[0],dz=s[3]-s[1],l=dx*dx+dz*dz||1,t=Math.max(0,Math.min(1,((x-s[0])*dx+(z-s[1])*dz)/l));if(Math.hypot(x-s[0]-dx*t,z-s[1]-dz*t)<s[4]+.3)return true}return false};
  const rib=(pts,hw,off,y0,col,dash,me,skip)=>{const C=rgb(col);let prev=null;
   for(let k=0;k<pts.length-1;k++){const a=pts[k],b=pts[k+1],L=Math.hypot(b[0]-a[0],b[1]-a[1]);if(L<.05)continue;const ux=(b[0]-a[0])/L,uz=(b[1]-a[1])/L,nx=-uz,nz=ux,ns=Math.max(1,Math.ceil(L/8));
    for(let s=0;s<ns;s++){const t0=s/ns,t1=(s+1)/ns;if(dash&&((k*7+s)%3)!=0)continue;
     const q=t=>{const x=a[0]+(b[0]-a[0])*t,z=a[1]+(b[1]-a[1])*t,y=a[2]!=null?a[2]+(b[2]-a[2])*t:ht(x,z);return[x,y,z]};
     const A=q(t0),Bq=q(t1);if(skip&&(skip(A[0]+nx*off,A[2]+nz*off)||skip(Bq[0]+nx*off,Bq[2]+nz*off)))continue;
     const v=[[A[0]+nx*(off-hw),A[1]+y0,A[2]+nz*(off-hw)],[A[0]+nx*(off+hw),A[1]+y0,A[2]+nz*(off+hw)],[Bq[0]+nx*(off+hw),Bq[1]+y0,Bq[2]+nz*(off+hw)],[Bq[0]+nx*(off-hw),Bq[1]+y0,Bq[2]+nz*(off-hw)]];
     for(const i of[0,1,2,0,2,3]){R.p.push(...v[i]);R.n.push(0,1,0);R.u.push(0,0);R.c.push(...C)}}}};
  /* v128 (regola fissa 8): cordolo verticale del marciapiede, dal bordo strada fino a +25 cm */
  const kerb=(pts,off,y0,y1,col,skip)=>{const C=rgb(col),sg=off>0?1:-1;
   for(let k=0;k<pts.length-1;k++){const a=pts[k],b=pts[k+1],L=Math.hypot(b[0]-a[0],b[1]-a[1]);if(L<.05)continue;const ux=(b[0]-a[0])/L,uz=(b[1]-a[1])/L,nx=-uz,nz=ux,ns=Math.max(1,Math.ceil(L/8));
    for(let s=0;s<ns;s++){const t0=s/ns,t1=(s+1)/ns,q=t=>{const x=a[0]+(b[0]-a[0])*t,z=a[1]+(b[1]-a[1])*t;return[x+nx*off,ht(x,z),z+nz*off]};const A=q(t0),Bq=q(t1);
     if(skip&&(skip(A[0]+nx*sg*.8,A[2]+nz*sg*.8)||skip(Bq[0]+nx*sg*.8,Bq[2]+nz*sg*.8)))continue;
     const v=[[A[0],A[1]+y0,A[2]],[Bq[0],Bq[1]+y0,Bq[2]],[Bq[0],Bq[1]+y1,Bq[2]],[A[0],A[1]+y1,A[2]]];
     for(const i of[0,1,2,0,2,3]){R.p.push(...v[i]);R.n.push(-nx*sg,0,-nz*sg);R.u.push(0,0);R.c.push(...C)}}}};
  const dense=d.b.length>25;
  RW.sort((a,b)=>b.c-a.c);
  for(const r of RW){const c=r.c,lift=r.br?.35:.06+(20-Math.min(c,20))*.004;
   if(c==20){rib(r.P,1.6,0,lift,COL[20]);rib(r.P,.05,.72,lift+.12,0x8f8f8f);rib(r.P,.05,-.72,lift+.12,0x8f8f8f);continue}
   rib(r.P,r.w/2,0,lift,COL[c]||0x48494c);
   if(c<=7&&r.w>=5.5){if(c<=1){rib(r.P,.08,r.w/2-.35,lift+.012,0xe8e8e2);rib(r.P,.08,-r.w/2+.35,lift+.012,0xe8e8e2)}else rib(r.P,.07,0,lift+.012,0xe8e8e2,1)}
   if(dense&&c>=2&&c<=7&&!r.br){const sw=1.7,so=r.w/2+sw/2;const sk2=(x,z)=>onOther(x,z,r);/* v135: marciapiede accorciato ai capi (incroci): prima a volte attraversava la strada vicina se stava nel quadrato accanto */const TP=trim(r.P,r.w/2+3);if(TP){rib(TP,sw/2,so,lift+.25,0xc7c1b4,0,r,sk2);rib(TP,sw/2,-so,lift+.25,0xc7c1b4,0,r,sk2);kerb(TP,r.w/2,lift,lift+.25,0xa9a59c,sk2);kerb(TP,-r.w/2,lift,lift+.25,0xa9a59c,sk2)}}}
  /* v137 (strade come a Pirri in tutta la mappa): strisce pedonali vere, linee di stop e di precedenza nei punti OSM, posizione dei semafori (d.x = [tipo,x,z,...]: 0 strisce, 1 semaforo, 2 stop, 3 dare precedenza) */
  const SIG=[];if(d.x&&d.x.length){const WC=rgb(0xeeeeea);
   const rect=(cx,cz,ux,uz,a0,a1,o0,o1,y0)=>{const nx=-uz,nz=ux,P=[[a0,o0],[a1,o0],[a1,o1],[a0,o1]].map(([a,o])=>{const x=cx+ux*a+nx*o,z=cz+uz*a+nz*o;return[x,ht(x,z)+y0,z]});for(const i of[0,1,2,0,2,3]){R.p.push(...P[i]);R.n.push(0,1,0);R.u.push(0,0);R.c.push(...WC)}};
   for(let k=0;k+2<d.x.length;k+=3){const ty=d.x[k],px=ox+d.x[k+1]/10,pz=oz+d.x[k+2]/10;let best=null,bd=1e9;
    for(let gi=-1;gi<=1;gi++)for(let gj=-1;gj<=1;gj++){const L2=SEG.get((Math.floor(px/12)+gi)+','+(Math.floor(pz/12)+gj));if(!L2)continue;for(const sg of L2){const r=sg[5];if(r.c>9||r.br)continue;const dx=sg[2]-sg[0],dz=sg[3]-sg[1],l=dx*dx+dz*dz||1,t=Math.max(0,Math.min(1,((px-sg[0])*dx+(pz-sg[1])*dz)/l)),qx=sg[0]+dx*t,qz=sg[1]+dz*t,dd=Math.hypot(px-qx,pz-qz);if(dd<bd&&dd<sg[4]+4){bd=dd;const L=Math.sqrt(l);best={x:qx,z:qz,ux:dx/L,uz:dz/L,w:r.w,r}}}}
    if(!best)continue;const {x,z,ux,uz,w,r}=best,lift=.06+(20-Math.min(r.c,20))*.004+.022;
    if(ty==0){if(w<4)continue;for(let o=-w/2+.55;o<=w/2-.45;o+=1)rect(x,z,ux,uz,-1.25,1.25,o,o+.5,lift)}
    else if(ty==1){for(const sd of[1,-1]){const o=(w/2+.7)*sd;SIG.push(x-uz*o,ht(x-uz*o,z+ux*o),z+ux*o,Math.atan2(-ux*sd,-uz*sd))}}
    else{/* verso l'incrocio: il capo della strada piu' vicino */const P0=r.P[0],P1=r.P[r.P.length-1],toEnd=Math.hypot(P1[0]-x,P1[1]-z)<Math.hypot(P0[0]-x,P0[1]-z)?1:-1,dx=ux*toEnd,dz=uz*toEnd;
     if(ty==2)rect(x,z,dx,dz,-.25,.25,0,w/2-.2,lift);else for(let o=.3;o<w/2-.3;o+=.9)rect(x,z,dx,dz,-.3,.3,o,o+.5,lift)}}}
  out.sig=new Float32Array(SIG);
  /* v137 (recinzioni come a Pirri): muri, recinzioni e siepi veri (d.f = [tipo,x0,z0,x1,z1,...]) */
  if(d.f&&d.f.length){const FC=[rgb(0xb9ad97),rgb(0x5d6166),rgb(0x3f5a2e),rgb(0xb8bcc0)],FH=[1.8,1.5,1.3,.8],FW=[.25,.05,.8,.1];
   const wall=(ax,az,bx,bz,h,w,C)=>{const L=Math.hypot(bx-ax,bz-az);if(L<.1)return;const ux=(bx-ax)/L,uz=(bz-az)/L,nx=-uz*w/2,nz=ux*w/2,ya=ht(ax,az)-.2,yb=ht(bx,bz)-.2;
    const S=[[ax+nx,az+nz,bx+nx,bz+nz,-uz,ux],[bx-nx,bz-nz,ax-nx,az-nz,uz,-ux]];for(const [x0,z0,x1,z1,qx,qz] of S){const P=[[x0,ya,z0],[x1,yb,z1],[x1,yb+h+.2,z1],[x0,ya+h+.2,z0]];for(const i of[0,1,2,0,2,3]){R.p.push(...P[i]);R.n.push(qx,0,qz);R.u.push(0,0);R.c.push(...C)}}
    if(w>.15){const P=[[ax+nx,ya+h,az+nz],[bx+nx,yb+h,bz+nz],[bx-nx,yb+h,bz-nz],[ax-nx,ya+h,az-nz]];for(const i of[0,1,2,0,2,3]){R.p.push(...P[i]);R.n.push(0,1,0);R.u.push(0,0);R.c.push(...C.map(v=>v*1.08))}}};
   for(let k=0;k+4<d.f.length;k+=5){const ty=d.f[k];wall(ox+d.f[k+1]/10,oz+d.f[k+2]/10,ox+d.f[k+3]/10,oz+d.f[k+4]/10,FH[ty],FW[ty],FC[ty])}}
  out.road=R.f();
  // --- edifici ---
  const W=new B(),RF=new B(),boxes=[];const Wd=2048,Hh=1024,RH=204;
  const quad=(x0,z0,x1,z1,a0,a1,b0,b1,nx,nz,col,row,v)=>{const e=2/Wd,u0=v/8+e,u1=(v+1)/8-e,vb=1-(row+1)*RH/Hh+1.5/Hh,vt=1-row*RH/Hh-1.5/Hh;
   W.p.push(x0,a0,z0,x1,a1,z1,x1,b1,z1,x0,a0,z0,x1,b1,z1,x0,b0,z0);W.u.push(u0,vb,u1,vb,u1,vt,u0,vb,u1,vt,u0,vt);for(let i=0;i<6;i++){W.n.push(nx,0,nz);W.c.push(col[0],col[1],col[2])}};
  /* v128: finestre e balconi per le finestre 3D vicine (FIN127): [x,y,z,nx,nz,w,h,tipo] e [x,y,z,nx,nz,w,parapetto] */
  const WN=[],BN=[],WU=[[[1.6,1,1.15,1.45],[5.7,1,1.15,1.45]],[[1.4,.1,1.1,2.3,1],[5.6,1,1.15,1.45]],[[.9,1,1.05,1.45],[3.7,1,1.05,1.45],[6.5,1,1.05,1.45]],[[1.6,.1,1.1,2.3,1],[5.8,.1,1.1,2.3,1]],
   [[.9,1,1.05,1.45],[3.7,.1,1.1,2.3,1],[6.5,1,1.05,1.45]],[[1.3,.1,1.1,2.3,1],[5.9,.1,1.1,2.3,1]],[[2,1,1.1,1.45],[5.4,1,1.1,1.45]]],
   WG=[[[5,1.05,1.15,1.4]],[],[[1,1.05,1.1,1.4],[6.4,1.05,1.1,1.4]],[],[[3.7,1.05,1.1,1.4]],[],[]],WB=[[],[[.9,2.1]],[],[[.8,6.9]],[[3,2.5]],[[.8,2.1],[5.4,2.1]],[]];
  const win128=(x0,z0,x1,z1,g0,top,fl,nx,nz,v)=>{const L=Math.hypot(x1-x0,z1-z0),dx=(x1-x0)/L,dz=(z1-z0)/L,su=L/8.5,fh=(top-g0)/fl,sv=fh/3.2;if(fh<2.2||fl>12)return;const y0=g0;
   for(let f=0;f<fl;f++){for(const q of(f==0?WG[v]:WU[v])){const tc=(q[0]+q[2]/2)*su,x=x0+dx*tc,z=z0+dz*tc,op=hs(x*3.1+z*7.7+f)<.3?16:0;WN.push(x,y0+f*fh+q[1]*sv,z,nx,nz,q[2]*su,q[3]*sv,v+(q[4]?8:0)+op)}
    if(f==0&&v==3){const tc=2.7*su;WN.push(x0+dx*tc,y0+2.72*sv,z0+dz*tc,nx,nz,4.3*su,.55,32)}
    if(f>0)for(const b of WB[v]){const tc=(b[0]+b[1]/2)*su;BN.push(x0+dx*tc,y0+f*fh,z0+dz*tc,nx,nz,(b[1]+.3)*su,v%2)}}};
  let bi=0;
  for(const b of d.b){bi++;const H=b[0]/10,rc=b[1],fl=b[2],sp=fl&7,n=b[3],P=[];for(let k=0;k<n;k++)P.push(ox+b[4+2*k]/10,oz+b[5+2*k]/10);
   let ar=0;for(let i=0;i<n;i++){const j=(i+1)%n;ar+=P[2*i]*P[2*j+1]-P[2*j]*P[2*i+1]}if(ar<0){const Q2=[];for(let i=n-1;i>=0;i--)Q2.push(P[2*i],P[2*i+1]);P.length=0;P.push(...Q2)}
   let gmin=1e9,gs=0;const GE=[];for(let i=0;i<n;i++){const g=ht(P[2*i],P[2*i+1]);GE.push(g);gmin=Math.min(gmin,g);gs+=g}
   const top=gs/n+H,sb=P[0]*13.7+P[1]*7.3,plain=sp==2||sp==3||sp==1||lod==0,floors=Math.max(1,Math.min(40,Math.round(H/3.2))),small=Math.abs(ar)/2<260;
   const base=sp==1?rgb(0xd8ccb2):sp==2?rgb(0xbab7b0):sp==3?rgb(0xb5b0a6):null;
   for(let i=0;i<n;i++){const j=(i+1)%n,ax=P[2*i],az=P[2*i+1],bx=P[2*j],bz=P[2*j+1],L=Math.hypot(bx-ax,bz-az);if(L<.05)continue;const nx=(bz-az)/L,nz=-(bx-ax)/L;
    const k=plain||L<3.4?1:Math.max(1,Math.round(L/(7+hs(sb+i)*3)));
    for(let s=0;s<k;s++){const t0=s/k,t1=(s+1)/k,x0=ax+(bx-ax)*t0,z0=az+(bz-az)*t0,x1=ax+(bx-ax)*t1,z1=az+(bz-az)*t1,g0=ht(x0,z0)-.3,g1=ht(x1,z1)-.3,sd=small?sb:sb+i*17.3+s*5.1;
     const col=base||rgb(PAL[Math.floor(hs(sd)*PAL.length)]),v=plain?7:Math.floor(hs(sd+3.3+i+s)*7);
     if(!plain&&v<7&&lod)win128(x0,z0,x1,z1,g0,top,floors,nx,nz,v);
     if(floors<=3||plain)quad(x0,z0,x1,z1,g0,g1,top,top,nx,nz,col,plain?0:floors-1,v);
     else{const T0=top-g0,T1=top-g1;let f=3;quad(x0,z0,x1,z1,g0,g1,g0+T0*3/floors,g1+T1*3/floors,nx,nz,col,2,v);while(f<floors){const c=floors-f>=2?2:1;quad(x0,z0,x1,z1,g0+T0*f/floors,g1+T1*f/floors,g0+T0*(f+c)/floors,g1+T1*(f+c)/floors,nx,nz,col,c==2?4:3,v);f+=c}}}}
   // tetto piano col colore vero preso dalla foto
   let rcol=rgb(rc||0xb8b2a6);rcol=rcol.map(c=>Math.min(1,c*1.08));const tr=ear(P);
   for(let q=0;q<tr.length;q+=3)for(const t of[tr[q],tr[q+2],tr[q+1]]){RF.p.push(P[2*t],top,P[2*t+1]);RF.n.push(0,1,0);RF.u.push(0,0);RF.c.push(...rcol)}
   // muretto in cima ai palazzi alti (parapetto)
   if(H>8&&sp==0&&lod){for(let i=0;i<n;i++){const j=(i+1)%n,ax=P[2*i],az=P[2*i+1],bx=P[2*j],bz=P[2*j+1],L=Math.hypot(bx-ax,bz-az);if(L<.5)continue;const nx=(bz-az)/L,nz=-(bx-ax)/L;quad(ax,az,bx,bz,top,top,top+.9,top+.9,nx,nz,rgb(0xe9e5dc),3,7)}}
   // urti: strisce di 3 m lungo z
   let zmin=1e9,zmax=-1e9;for(let i=0;i<n;i++){zmin=Math.min(zmin,P[2*i+1]);zmax=Math.max(zmax,P[2*i+1])}
   for(let zc=zmin+1.5;zc<zmax+1.4;zc+=3){const zz=Math.min(zc,zmax-.01),xs=[];for(let i=0;i<n;i++){const j=(i+1)%n,az=P[2*i+1],bz=P[2*j+1];if((az<=zz)!=(bz<=zz)){xs.push(P[2*i]+(zz-az)/(bz-az)*(P[2*j]-P[2*i]))}}xs.sort((a,b)=>a-b);for(let k=0;k+1<xs.length;k+=2)if(xs[k+1]-xs[k]>.3)boxes.push(xs[k],zz-1.5,xs[k+1],zz+1.5,top)}}
  out.walls=W.f();out.roofs=RF.f();out.boxes=new Float32Array(boxes);out.win=new Float32Array(WN);out.bal=new Float32Array(BN);
  // --- alberi ---
  const tr=[],tstep=2;/* v135: stessi alberi anche nei quadrati lontani (prima 1 su 3: avvicinandosi 'spuntavano' gli altri) */for(let k=0;k+1<d.t.length;k+=tstep){const x=ox+d.t[k]/10,z=oz+d.t[k+1]/10;tr.push(x,ht(x,z),z,.8+hs(x*3.1+z)*.7)}out.trees=new Float32Array(tr);/* v135: cespugli (macchia e giardini) */const bu=[];if(d.u)for(let k=0;k+1<d.u.length;k+=lod?2:4){const x=ox+d.u[k]/10,z=oz+d.u[k+1]/10,s=.6+hs(x*1.7+z*.3)*.9;bu.push(x,ht(x,z)+.4*s,z,s)}out.bush=new Float32Array(bu);
  return out}
 self.onmessage=async e=>{const m=e.data;
  if(m.t=='init'){Q=m.Q;QH=m.QH;postMessage({t:'ok'});return}
  if(m.t=='tile'){try{const [i,j]=m.key.split('_').map(Number),bk=Math.floor(i/m.bs)+'_'+Math.floor(j/m.bs);
    let pr=BC.get(bk);if(!pr){/* v137: se il secondo sito non risponde, riserva sul sito del gioco (m.u2) */const F2=u=>fetch(m.url+u).then(r=>{if(!r.ok)throw 0;return r}).catch(e=>m.u2&&m.u2!=m.url?fetch(m.u2+u):Promise.reject(e));pr=F2('b_'+bk+'.json').then(r=>r.json());BC.set(bk,pr);if(BC.size>10)BC.delete(BC.keys().next().value)}
    const d=Object.assign({},(await pr)[m.key]);d.key=m.key;d.core=m.core;
    let img=null;/* v137: foto del quadrato in un file .jpg a parte (mondo/img/t_I_J.jpg) */if(d.im){try{const r=await fetch(m.url+'img/t_'+m.key+'.jpg').then(r=>r.ok||!m.u2||m.u2==m.url?r:fetch(m.u2+'img/t_'+m.key+'.jpg'),()=>m.u2?fetch(m.u2+'img/t_'+m.key+'.jpg'):null);if(r.ok)img=await createImageBitmap(await r.blob())}catch(er){}}if(d.img){try{const bs=atob(d.img),u8=new Uint8Array(bs.length);for(let q=0;q<bs.length;q++)u8[q]=bs.charCodeAt(q);img=await createImageBitmap(new Blob([u8],{type:'image/jpeg'}))}catch(er){}}delete d.img;
    const o=build(d,m.lod);o.img=img;o.data=d;const tf=[];for(const k of['ground','water','road','walls','roofs'])if(o[k])for(const a of Object.values(o[k]))tf.push(a.buffer);tf.push(o.boxes.buffer,o.trees.buffer,o.win.buffer,o.bal.buffer,o.bush.buffer,o.sig.buffer);if(img)tf.push(img);
    postMessage(o,tf)}catch(er){postMessage({key:m.key,err:String(er)})}}
  if(m.t=='lod'){try{const o=build(Object.assign({},m.d,{g:0}),m.lod);const tf=[];for(const k of['road','walls','roofs'])for(const a of Object.values(o[k]))tf.push(a.buffer);tf.push(o.boxes.buffer,o.trees.buffer,o.win.buffer,o.bal.buffer,o.bush.buffer,o.sig.buffer);delete o.ground;delete o.water;o.relod=1;postMessage(o,tf)}catch(er){postMessage({key:m.key,err:String(er)})}}};