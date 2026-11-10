
 let Q=null,QH=null;const BC=new Map(),FQ=new Map();let FB=0;
 const decQ=q=>{const b=atob(q.h),a=new Int16Array(b.length>>1);for(let i=0;i<a.length;i++)a[i]=((b.charCodeAt(2*i)|(b.charCodeAt(2*i+1)<<8))<<16)>>16;return{x0:q.x0,z0:q.z0,s:q.s,nx:q.nx,nz:q.nz,a}};
 const gq=(x,z)=>{if(FB){const f=FQ.get(Math.floor(x/FB)+'_'+Math.floor(z/FB));if(f&&x>=f.x0&&z>=f.z0&&x<=f.x0+(f.nx-1.001)*f.s&&z<=f.z0+(f.nz-1.001)*f.s)return f}return null};
 const hq=(x,z)=>{const F=gq(x,z),Q_=F||Q,A=F?F.a:QH;let u=(x-Q_.x0)/Q_.s,v=(z-Q_.z0)/Q_.s;u=u<0?0:u>Q_.nx-1.001?Q_.nx-1.001:u;v=v<0?0:v>Q_.nz-1.001?Q_.nz-1.001:v;const i=u|0,j=v|0,fu=u-i,fv=v-j,k=j*Q_.nx+i;return(A[k]*(1-fu)*(1-fv)+A[k+1]*fu*(1-fv)+A[k+Q_.nx]*(1-fu)*fv+A[k+Q_.nx+1]*fu*fv)/10};
 const ht=(x,z)=>{const F=gq(x,z),Q_=F||Q,A=F?F.a:QH;let u=(x-Q_.x0)/Q_.s,v=(z-Q_.z0)/Q_.s;u=u<0?0:u>Q_.nx-1.001?Q_.nx-1.001:u;v=v<0?0:v>Q_.nz-1.001?Q_.nz-1.001:v;const i=u|0,j=v|0,fu=u-i,fv=v-j,k=j*Q_.nx+i,a=A[k]/10,b=A[k+1]/10,c=A[k+Q_.nx]/10,d=A[k+Q_.nx+1]/10;
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
  /* v150: zone dei monumenti rifatti a mano (d.ex = [x,z,raggio,...]): li' edifici e muri generici non si costruiscono */
  const exz=(x,z)=>{const E=d.ex;if(!E)return false;for(let q=0;q<E.length;q+=3)if(Math.hypot(x-E[q],z-E[q+1])<E[q+2])return true;return false};
  // --- terreno con la foto (salta la parte gia' coperta dalla mappa di Pirri e dalla sua cornice) ---
  if(d.g){const S=20,N=T/S+1,p=new Float32Array(N*N*3),u=new Float32Array(N*N*2),n=new Float32Array(N*N*3),I=[];
   for(let j=0;j<N;j++)for(let i=0;i<N;i++){const x=ox+i*S,z=oz+j*S,k=j*N+i;p[3*k]=x;p[3*k+1]=hq(x,z);p[3*k+2]=z;u[2*k]=i/(N-1);u[2*k+1]=j/(N-1);
    const dx=hq(x+S,z)-hq(x-S,z),dz=hq(x,z+S)-hq(x,z-S),l=Math.hypot(dx,2*S,dz);n[3*k]=-dx/l;n[3*k+1]=2*S/l;n[3*k+2]=-dz/l}
   for(let j=0;j<N-1;j++)for(let i=0;i<N-1;i++){const ax0=ox+i*S,az0=oz+j*S;if(ax0>=core[0]&&ax0+S<=core[2]&&az0>=core[1]&&az0+S<=core[3])continue;const k=j*N+i;I.push(k,k+N,k+1,k+1,k+N,k+N+1)}
   out.ground={p,u,n,i:new Uint32Array(I)}}
  // --- acqua (mare, stagni, saline): superficie piana a quota 0 sulle celle bagnate ---
  if(d.wm){const S=20,N=T/S+1,P=[],wet=(i,j)=>i>=0&&j>=0&&i<N&&j<N&&((d.wm[j]>>i)&1);const U=[],wt=(i,j)=>i<0||j<0||i>=N||j>=N||((d.wm[j]>>i)&1),sh=(i,j)=>{/* v143: riva per la schiuma (1 = punto asciutto, poi 0,6 / 0,25 a 1-2 celle) */if(!wt(i,j))return 1;let m=0;for(let r=1;r<=2&&!m;r++)for(let b=-r;b<=r;b++)for(let a=-r;a<=r;a++)if(!wt(i+a,j+b)){m=r==1?.6:.25}return m};
   for(let j=0;j<N-1;j++)for(let i=0;i<N-1;i++){if(!(wet(i,j)||wet(i+1,j)||wet(i,j+1)||wet(i+1,j+1)))continue;const x0=ox+i*S,z0=oz+j*S;if(x0>=core[0]&&x0+S<=core[2]&&z0>=core[1]&&z0+S<=core[3])continue;P.push(x0,0,z0,x0,0,z0+S,x0+S,0,z0,x0+S,0,z0,x0,0,z0+S,x0+S,0,z0+S);for(const[a,b]of[[i,j],[i,j+1],[i+1,j],[i+1,j],[i,j+1],[i+1,j+1]])U.push(sh(a,b),7)}
   if(P.length){const p=new Float32Array(P),n=new Float32Array(P.length);for(let q=1;q<n.length;q+=3)n[q]=1;out.water={p,n,u:new Float32Array(U),c:new Float32Array(0)}}}
  // --- strade: nastri che seguono il terreno, strisce di mezzeria e marciapiedi ---
  const R=new B(),SEG=new Map(),sk=(x,z)=>Math.floor(x/12)+','+Math.floor(z/12);
  const COL={0:0x45474b,1:0x45474b,2:0x3e4044,3:0x3e4044,4:0x404246,5:0x404246,6:0x46484b,7:0x48494c,9:0x55565a,10:0xb4ada0,11:0x9a5a4a,12:0x9a8868,13:0xbdb5a5,14:0xa9a397,15:0x9f9070,20:0x6d655b};
  const RW=d.r.map(r=>{const c=r[0],w=r[1]/10,fl=r[2],br=fl&1,st=br?3:2,P=[];for(let k=4;k+1<r.length;k+=st)P.push([ox+r[k]/10,oz+r[k+1]/10,br?r[k+2]/10:null]);return{c,w,br,P}});
  /* v149: nell'indice delle carreggiate entrano anche le strade dei quadrati accanto (d.nb, dallo stesso pacchetto o da quelli gia' scaricati): prima un marciapiede non "vedeva" la strada del quadrato vicino.
     Ogni tratto e' registrato in TUTTE le celle che tocca (prima solo in quelle dei suoi punti: una strada larga vicino al bordo di una cella non veniva trovata). */
  const RN=[];for(const q of(d.nb||[]))for(const r of q.r){const c=r[0],br=r[2]&1,st=br?3:2,P=[];for(let k=4;k+1<r.length;k+=st)P.push([q.o[0]+r[k]/10,q.o[1]+r[k+1]/10,null]);RN.push({c,w:r[1]/10,br,P,nb:1})}
  for(const r of RW.concat(RN)){if(r.c>=10&&r.c!=13)continue;const m=r.w/2+1.5;let arc=0;for(let k=0;k<r.P.length-1;k++){const a=r.P[k],b=r.P[k+1],a0=arc;arc+=Math.hypot(b[0]-a[0],b[1]-a[1]);if(r.nb&&Math.max(a[0],b[0])<ox-40||Math.min(a[0],b[0])>ox+T+40||Math.max(a[1],b[1])<oz-40||Math.min(a[1],b[1])>oz+T+40)continue;
    const e=[a[0],a[1],b[0],b[1],r.w/2,r,a0,arc],i0=Math.floor((Math.min(a[0],b[0])-m)/12),i1=Math.floor((Math.max(a[0],b[0])+m)/12),j0=Math.floor((Math.min(a[1],b[1])-m)/12),j1=Math.floor((Math.max(a[1],b[1])+m)/12);
    for(let i=i0;i<=i1;i++)for(let j=j0;j<=j1;j++){const key=i+','+j;let L2=SEG.get(key);if(!L2)SEG.set(key,L2=[]);L2.push(e)}}}
  /* sa = posizione lungo la propria strada: cosi' conta anche un ALTRO tratto della stessa strada (anelli di inversione, tornanti stretti), non quello dove si e' */
  const onOther=(x,z,me,mg,sa)=>{const L2=SEG.get(sk(x,z));if(!L2)return false;const g=mg==null?.3:mg;for(const s of L2){if(s[5].br||(s[5]===me&&sa==null))continue;const dx=s[2]-s[0],dz=s[3]-s[1],l=dx*dx+dz*dz||1,t=Math.max(0,Math.min(1,((x-s[0])*dx+(z-s[1])*dz)/l));if(s[5]===me&&Math.abs(s[6]+(s[7]-s[6])*t-sa)<me.w+8)continue;if(Math.hypot(x-s[0]-dx*t,z-s[1]-dz*t)<s[4]+g)return true}return false};
  /* v149 STRADE NUOVE. Prima ogni strada era un nastro PIATTO di traverso alla quota del suo centro: sui pendii un bordo restava sotto il terreno e l'altro sospeso (e le auto, che seguono il terreno, sembravano sospese o affondate);
     nelle curve e nelle rotonde tra un pezzo e l'altro restavano spicchi vuoti. Ora: sezioni ogni 5 m (e a ogni punto della strada) con la normale "a smusso" nelle curve -> nastro continuo;
     ogni punto della carreggiata segue il terreno (a strisce di 3,6 m di traverso); righe disegnate sulla superficie vera della strada; ponti con quota propria, parapetti e fianco. */
  const resamp=(P,step)=>{const o=[];let s=0;for(let k=0;k<P.length-1;k++){const a=P[k],b=P[k+1],L=Math.hypot(b[0]-a[0],b[1]-a[1]);if(L<.05)continue;const n=Math.max(1,Math.ceil(L/step));
     for(let i=o.length?1:0;i<=n;i++){const t=i/n;o.push([a[0]+(b[0]-a[0])*t,a[1]+(b[1]-a[1])*t,a[2]!=null?a[2]+(b[2]-a[2])*t:null,s+L*t,0,0])}s+=L}
    const n=o.length;for(let i=0;i<n;i++){const p=o[Math.max(0,i-1)],q=o[Math.min(n-1,i+1)],c=o[i];let ax=c[0]-p[0],az=c[1]-p[1],bx=q[0]-c[0],bz=q[1]-c[1];const la=Math.hypot(ax,az),lb=Math.hypot(bx,bz);
     if(la>1e-6){ax/=la;az/=la}if(lb>1e-6){bx/=lb;bz/=lb}if(la<=1e-6){ax=bx;az=bz}if(lb<=1e-6){bx=ax;bz=az}let tx=ax+bx,tz=az+bz;const lt=Math.hypot(tx,tz);if(lt<1e-6){tx=ax;tz=az}else{tx/=lt;tz/=lt}
     const ch=Math.max(.62,tx*ax+tz*az);c[4]=-tz/ch;c[5]=tx/ch}return o};
  const push=(v,C,nx,ny,nz)=>{for(const q of[0,1,2,0,2,3]){R.p.push(v[q][0],v[q][1],v[q][2]);R.n.push(nx,ny,nz);R.u.push(0,0);R.c.push(C[0],C[1],C[2])}};
  /* quota della superficie della carreggiata nella sezione c, a distanza o dal centro (c[6] = quote ai bordi delle strisce) */
  const surf=(c,o)=>{const Y=c[6],hw=c[7],ns=Y.length-1,f=Math.max(0,Math.min(ns-1e-6,(o+hw)/(2*hw)*ns)),j=f|0;return Y[j]+(Y[j+1]-Y[j])*(f-j)};
  const deck=(S,hw,y0,col)=>{const C=rgb(col),ns=2*hw<=5.6?1:Math.ceil(2*hw/4.2);for(const c of S){const Y=[];for(let j=0;j<=ns;j++){const o=-hw+2*hw*j/ns;Y.push((c[2]!=null?c[2]:ht(c[0]+c[4]*o,c[1]+c[5]*o))+y0)}c[6]=Y;c[7]=hw}
   for(let i=0;i<S.length-1;i++){const a=S[i],b=S[i+1];for(let j=0;j<ns;j++){const u0=-hw+2*hw*j/ns,u1=-hw+2*hw*(j+1)/ns;
     push([[a[0]+a[4]*u0,a[6][j],a[1]+a[5]*u0],[a[0]+a[4]*u1,a[6][j+1],a[1]+a[5]*u1],[b[0]+b[4]*u1,b[6][j+1],b[1]+b[5]*u1],[b[0]+b[4]*u0,b[6][j],b[1]+b[5]*u0]],C,0,1,0)}}};
  /* riga dipinta sulla carreggiata (tra o0 e o1 dal centro), solo nei tratti dove ok(i) */
  const paint=(S,o0,o1,dy,col,ok)=>{const C=rgb(col),V=(c,o)=>[c[0]+c[4]*o,surf(c,o)+dy,c[1]+c[5]*o];for(let i=0;i<S.length-1;i++){if(ok&&!ok(i))continue;const a=S[i],b=S[i+1];push([V(a,o0),V(a,o1),V(b,o1),V(b,o0)],C,0,1,0)}};
  /* muretto verticale lungo la strada a distanza o dal centro, da ya a yb sopra la superficie (visibile dai due lati) */
  const fence=(S,o,ya,yb,col)=>{const C=rgb(col),sg=o>0?1:-1;for(let i=0;i<S.length-1;i++){const a=S[i],b=S[i+1],A=[a[0]+a[4]*o,surf(a,o),a[1]+a[5]*o],Bq=[b[0]+b[4]*o,surf(b,o),b[1]+b[5]*o];
    const v=[[A[0],A[1]+ya,A[2]],[Bq[0],Bq[1]+ya,Bq[2]],[Bq[0],Bq[1]+yb,Bq[2]],[A[0],A[1]+yb,A[2]]];push(v,C,-a[4]*sg,0,-a[5]*sg);push([v[1],v[0],v[3],v[2]],C,a[4]*sg,0,a[5]*sg)}};
  /* marciapiede rialzato di 25 cm (regola fissa) da un lato: lastra che segue il terreno, cordolo verso la strada, fianco esterno e testate.
     Si interrompe ESATTAMENTE dove entra nella carreggiata di un'altra strada (controllo ogni metro su bordo interno, centro e bordo esterno; taglio trovato a 10 cm):
     agli incroci i marciapiedi delle due strade arrivano fino all'angolo e si chiudono, e non attraversano mai una strada. */
  const walk=(S,r,sg)=>{const hw=r.w/2,sw=1.7,KH=.25,CS=rgb(0xc7c1b4),CK=rgb(0xa9a59c);
   const sec=(i,t)=>{const a=S[i],b=S[Math.min(S.length-1,i+1)];const c=[a[0]+(b[0]-a[0])*t,a[1]+(b[1]-a[1])*t,null,a[3]+(b[3]-a[3])*t,a[4]+(b[4]-a[4])*t,a[5]+(b[5]-a[5])*t];c[8]=surf(a,sg*hw)+(surf(b,sg*hw)-surf(a,sg*hw))*t;return c};
   const free=c=>{for(const o of[hw+.12,hw+sw*.5,hw+sw-.1]){if(onOther(c[0]+c[4]*sg*o,c[1]+c[5]*sg*o,r,.02,c[3]))return false}return true};
   const runs=[];let cur=null,prev=null;/* prev = [i,t,libero] */
   const edge=(p,q)=>{let a=p,b=q;for(let k=0;k<5;k++){const m=[a[0],(a[1]+b[1])/2];if(a[0]!==b[0]){/* punti su tratti diversi: si resta sul primo */m[0]=a[0];m[1]=(a[1]+(b[0]>a[0]?1:b[1]))/2}if(free(sec(m[0],m[1]))===p[2])a=[m[0],m[1],p[2]];else b=[m[0],m[1],!p[2]]}return p[2]?a:b};
   for(let i=0;i<S.length-1;i++){const L=S[i+1][3]-S[i][3],n=Math.max(1,Math.ceil(L/1));for(let k=(i?1:0);k<=n;k++){const t=k/n,f=free(sec(i,t)),now=[i,t,f];
     if(f&&!cur){const e=prev?edge(now,prev):now;cur=[sec(e[0],e[1])]}
     if(!f&&cur){const e=edge(prev,now);cur.push(sec(e[0],e[1]));runs.push(cur);cur=null}
     else if(f&&cur&&k==n&&i<S.length-2)cur.push(sec(i+1,0));
     prev=now}}
   if(cur){cur.push(sec(S.length-2,1));runs.push(cur)}
   for(const Q of runs){if(Q.length<2)continue;const V=Q.map(c=>{const xi=c[0]+c[4]*sg*hw,zi=c[1]+c[5]*sg*hw,xo=c[0]+c[4]*sg*(hw+sw),zo=c[1]+c[5]*sg*(hw+sw),yi=c[8],yo=ht(xo,zo);return{xi,zi,xo,zo,yi,yo,nx:c[4]*sg,nz:c[5]*sg}});
    const cap=(a,f)=>{const v=[[a.xi,a.yi,a.zi],[a.xo,a.yo-.02,a.zo],[a.xo,Math.max(a.yo+.06,a.yi)+KH,a.zo],[a.xi,a.yi+KH,a.zi]];push(f?v:[v[1],v[0],v[3],v[2]],CK,0,1,0)};
    for(let i=0;i<V.length-1;i++){const a=V[i],b=V[i+1];if(Math.hypot(b.xi-a.xi,b.zi-a.zi)<.03)continue;const ta=Math.max(a.yo+.06,a.yi)+KH,tb=Math.max(b.yo+.06,b.yi)+KH;
     const top=[[a.xi,a.yi+KH,a.zi],[a.xo,ta,a.zo],[b.xo,tb,b.zo],[b.xi,b.yi+KH,b.zi]];push(sg>0?top:[top[1],top[0],top[3],top[2]],CS,0,1,0);
     const kb=[[a.xi,a.yi,a.zi],[b.xi,b.yi,b.zi],[b.xi,b.yi+KH,b.zi],[a.xi,a.yi+KH,a.zi]];push(sg>0?kb:[kb[1],kb[0],kb[3],kb[2]],CK,-a.nx,0,-a.nz);
     const ob=[[b.xo,b.yo-.02,b.zo],[a.xo,a.yo-.02,a.zo],[a.xo,ta,a.zo],[b.xo,tb,b.zo]];push(sg>0?ob:[ob[1],ob[0],ob[3],ob[2]],CK,a.nx,0,a.nz)}
    cap(V[0],sg>0);cap(V[V.length-1],sg<0)}};
  const dense=d.b.length>25;
  RW.sort((a,b)=>b.c-a.c);
  for(const r of RW){const c=r.c,lift=r.br?.35:.06+(20-Math.min(c,20))*.004,S=resamp(r.P,7);if(S.length<2)continue;
   if(c==20){deck(S,1.6,lift,COL[20]);paint(S,.67,.77,.12,0x8f8f8f);paint(S,-.77,-.67,.12,0x8f8f8f);continue}
   deck(S,r.w/2,lift,COL[c]||0x48494c);
   if(c<=7&&r.w>=5.5){if(c<=1){paint(S,r.w/2-.43,r.w/2-.27,.02,0xe8e8e2);paint(S,-r.w/2+.27,-r.w/2+.43,.02,0xe8e8e2)}
    else paint(S,-.07,.07,.02,0xe8e8e2,i=>(Math.floor(S[i][3]/7+.01)%2)==0&&S[i+1][3]-S[i][3]>2.5&&!onOther((S[i][0]+S[i+1][0])/2,(S[i][1]+S[i+1][1])/2,r,1))}
   if(r.br){for(const sg of[1,-1]){fence(S,sg*(r.w/2+.12),0,1.05,0x9c9c97);fence(S,sg*(r.w/2+.13),-.8,0,0x8a8a86)}}
   if(dense&&c>=2&&c<=7&&!r.br){walk(S,r,1);walk(S,r,-1)}}
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
  /* v139: parcheggi veri (OSM, d.k = [tipo,n,x,z,...]): asfalto a celle da 4 m che seguono il terreno + strisce bianche dei posti (2,5 m) lungo i lati */
  if(d.k&&d.k.length){const AC=rgb(0x3d3e40),WC2=rgb(0xe6e6e0);const tri=(A,B,C,col)=>{for(const q of[A,B,C]){R.p.push(q[0],q[1],q[2]);R.n.push(0,1,0);R.u.push(0,0);R.c.push(...col)}};
   for(const pk of d.k){const n=pk[1],X=[],Z=[];for(let q=0;q<n;q++){X.push(ox+pk[2+2*q]/10);Z.push(oz+pk[3+2*q]/10)}
    const inP=(x,z)=>{let c=false;for(let i=0,j=n-1;i<n;j=i++)if((Z[i]>z)!=(Z[j]>z)&&x<(X[j]-X[i])*(z-Z[i])/(Z[j]-Z[i])+X[i])c=!c;return c};
    let x0=1e9,x1=-1e9,z0=1e9,z1=-1e9;for(let q=0;q<n;q++){x0=Math.min(x0,X[q]);x1=Math.max(x1,X[q]);z0=Math.min(z0,Z[q]);z1=Math.max(z1,Z[q])}
    const G=4,L=.07;for(let x=x0;x<x1;x+=G)for(let z=z0;z<z1;z+=G){const cx=x+G/2,cz=z+G/2;if(!inP(cx,cz))continue;const A=[x,ht(x,z)+L,z],B=[x+G,ht(x+G,z)+L,z],C=[x+G,ht(x+G,z+G)+L,z+G],D=[x,ht(x,z+G)+L,z+G];tri(A,C,B,AC);tri(A,D,C,AC)}
    for(let q=0;q<n;q++){const ax=X[q],az=Z[q],bx=X[(q+1)%n],bz=Z[(q+1)%n],l=Math.hypot(bx-ax,bz-az);if(l<8)continue;const ux=(bx-ax)/l,uz=(bz-az)/l,nx=uz,nz=-ux;/* interno = a destra del lato (poligono antiorario: verso -normale esterna) */
     const ix=-nx,iz=-nz;for(let t=1.2;t<l-1.2;t+=2.5){const sx=ax+ux*t+ix*.4,sz=az+uz*t+iz*.4,ex=sx+ix*4.6,ez=sz+iz*4.6;if(!inP(sx+ix*.2,sz+iz*.2)||!inP(ex,ez))continue;const w=.06,px=-iz*w,pz=ix*w,y1=ht(sx,sz)+L+.012,y2=ht(ex,ez)+L+.012;
      const A=[sx+px,y1,sz+pz],B=[ex+px,y2,ez+pz],C=[ex-px,y2,ez-pz],D=[sx-px,y1,sz-pz];tri(A,C,B,WC2);tri(A,D,C,WC2);tri(A,B,C,WC2);tri(A,C,D,WC2)}}}}
  /* v137 (recinzioni come a Pirri): muri, recinzioni e siepi veri (d.f = [tipo,x0,z0,x1,z1,...]) */
  if(d.f&&d.f.length){const FC=[rgb(0xb9ad97),rgb(0x5d6166),rgb(0x3f5a2e),rgb(0xb8bcc0)],FH=[1.8,1.5,1.3,.8],FW=[.25,.05,.8,.1];
   const wall=(ax,az,bx,bz,h,w,C)=>{const L=Math.hypot(bx-ax,bz-az);if(L<.1)return;const ux=(bx-ax)/L,uz=(bz-az)/L,nx=-uz*w/2,nz=ux*w/2,ya=ht(ax,az)-.2,yb=ht(bx,bz)-.2;
    const S=[[ax+nx,az+nz,bx+nx,bz+nz,-uz,ux],[bx-nx,bz-nz,ax-nx,az-nz,uz,-ux]];for(const [x0,z0,x1,z1,qx,qz] of S){const P=[[x0,ya,z0],[x1,yb,z1],[x1,yb+h+.2,z1],[x0,ya+h+.2,z0]];for(const i of[0,1,2,0,2,3]){R.p.push(...P[i]);R.n.push(qx,0,qz);R.u.push(0,0);R.c.push(...C)}}
    if(w>.15){const P=[[ax+nx,ya+h,az+nz],[bx+nx,yb+h,bz+nz],[bx-nx,yb+h,bz-nz],[ax-nx,ya+h,az-nz]];for(const i of[0,1,2,0,2,3]){R.p.push(...P[i]);R.n.push(0,1,0);R.u.push(0,0);R.c.push(...C.map(v=>v*1.08))}}};
   for(let k=0;k+4<d.f.length;k+=5){const ty=d.f[k];if(exz(ox+d.f[k+1]/10,oz+d.f[k+2]/10))continue;wall(ox+d.f[k+1]/10,oz+d.f[k+2]/10,ox+d.f[k+3]/10,oz+d.f[k+4]/10,FH[ty],FW[ty],FC[ty])}}
  out.road=R.f();
  // --- edifici ---
  const W=new B(),RF=new B(),boxes=[];const Wd=2048,Hh=1024,RH=204;
  const quad=(x0,z0,x1,z1,a0,a1,b0,b1,nx,nz,col,row,v)=>{const e=2/Wd,u0=v/8+e,u1=(v+1)/8-e,vb=1-(row+1)*RH/Hh+1.5/Hh,vt=1-row*RH/Hh-1.5/Hh;
   W.p.push(x0,a0,z0,x1,a1,z1,x1,b1,z1,x0,a0,z0,x1,b1,z1,x0,b0,z0);W.u.push(u0,vb,u1,vb,u1,vt,u0,vb,u1,vt,u0,vt);for(let i=0;i<6;i++){W.n.push(nx,0,nz);W.c.push(col[0],col[1],col[2])}};
  /* v138: tetto a due falde (solo poligoni convessi): colmo lungo il lato piu' lungo, le due falde sono piani esatti; timpani riempiti col colore della facciata */
  const tri138=(ax,ay,az,bx,by,bz,cx,cy,cz,col)=>{const ux=bx-ax,uy=by-ay,uz=bz-az,vx=cx-ax,vy=cy-ay,vz=cz-az;let nx=uy*vz-uz*vy,ny=uz*vx-ux*vz,nz=ux*vy-uy*vx;if(ny<0){nx=-nx;ny=-ny;nz=-nz;RF.p.push(ax,ay,az,cx,cy,cz,bx,by,bz)}else RF.p.push(ax,ay,az,bx,by,bz,cx,cy,cz);const l=Math.hypot(nx,ny,nz)||1;for(let i=0;i<3;i++){RF.n.push(nx/l,ny/l,nz/l);RF.u.push(0,0);RF.c.push(col[0],col[1],col[2])}};
  function roof138(P,n,top,rcol,wcol,slope,maxR){if(n<3||n>12)return 0;let sg=0;for(let i=0;i<n;i++){const a=i,b=(i+1)%n,c=(i+2)%n,cr=(P[2*b]-P[2*a])*(P[2*c+1]-P[2*b+1])-(P[2*b+1]-P[2*a+1])*(P[2*c]-P[2*b]);if(cr<-1e-3)return 0}
   let bl=0,ux=1,uz=0,cx=0,cz=0;for(let i=0;i<n;i++){const j=(i+1)%n,dx=P[2*j]-P[2*i],dz=P[2*j+1]-P[2*i+1],L=Math.hypot(dx,dz);cx+=P[2*i]/n;cz+=P[2*i+1]/n;if(L>bl){bl=L;ux=dx/L;uz=dz/L}}
   const vx=-uz,vz=ux,D=[];let dmin=1e9,dmax=-1e9;for(let i=0;i<n;i++){const d=(P[2*i]-cx)*vx+(P[2*i+1]-cz)*vz;D.push(d);dmin=Math.min(dmin,d);dmax=Math.max(dmax,d)}
   const d0=(dmin+dmax)/2,hw=(dmax-dmin)/2;if(hw<1.5||hw>16)return 0;const R=Math.min(maxR,hw*slope),hy=d=>top+R*(1-Math.abs(d-d0)/hw);
   for(const sd of[1,-1]){const Q=[];for(let i=0;i<n;i++){const j=(i+1)%n,a=(D[i]-d0)*sd,b=(D[j]-d0)*sd;if(a>=0)Q.push(P[2*i],P[2*i+1],D[i]);if((a>0&&b<0)||(a<0&&b>0)){const t=a/(a-b);Q.push(P[2*i]+(P[2*j]-P[2*i])*t,P[2*i+1]+(P[2*j+1]-P[2*i+1])*t,d0)}}
    const m=Q.length/3;if(m<3)continue;for(let k=1;k+1<m;k++)tri138(Q[0],hy(Q[2]),Q[1],Q[3*k],hy(Q[3*k+2]),Q[3*k+1],Q[3*k+3],hy(Q[3*k+5]),Q[3*k+4],rcol)}
   for(let i=0;i<n;i++){const j=(i+1)%n,L=Math.hypot(P[2*j]-P[2*i],P[2*j+1]-P[2*i+1]);if(L<.05)continue;const nx=(P[2*j+1]-P[2*i+1])/L,nz=-(P[2*j]-P[2*i])/L;
    const pts=[[P[2*i],P[2*i+1],D[i]]];if((D[i]-d0)*(D[j]-d0)<0){const t=(D[i]-d0)/(D[i]-D[j]);pts.push([P[2*i]+(P[2*j]-P[2*i])*t,P[2*i+1]+(P[2*j+1]-P[2*i+1])*t,d0])}pts.push([P[2*j],P[2*j+1],D[j]]);
    for(let k=0;k+1<pts.length;k++){const A=pts[k],B=pts[k+1],h0=hy(A[2]),h1=hy(B[2]);if(Math.max(h0,h1)-top>.05)quad(A[0],A[1],B[0],B[1],top,top,h0,h1,nx,nz,wcol,3,7)}}
   return {cx,cz,ux,uz,vx,vz,d0,hw,R,bl}}
  /* v143: sui tetti come in Sardegna: comignoli sui tetti a falde, pannelli solari termici col serbatoio bianco e cisterne dell'acqua sui tetti piani */
  const tri143=(ax,ay,az,bx,by,bz,cx,cy,cz,hx,hy2,hz,col)=>{const ux=bx-ax,uy=by-ay,uz=bz-az,vx=cx-ax,vy=cy-ay,vz=cz-az;let nx=uy*vz-uz*vy,ny=uz*vx-ux*vz,nz=ux*vy-uy*vx;if(nx*hx+ny*hy2+nz*hz<0){nx=-nx;ny=-ny;nz=-nz;RF.p.push(ax,ay,az,cx,cy,cz,bx,by,bz)}else RF.p.push(ax,ay,az,bx,by,bz,cx,cy,cz);const l=Math.hypot(nx,ny,nz)||1;for(let i=0;i<3;i++){RF.n.push(nx/l,ny/l,nz/l);RF.u.push(0,0);RF.c.push(col[0],col[1],col[2])}};
  const q143=(A,Bq,C,D,h,col)=>{tri143(...A,...Bq,...C,...h,col);tri143(...A,...C,...D,...h,col)};
  function box143(cx,cz,y0,y1,a,b,ux,uz,col){const vx=-uz,vz=ux,c=[];for(const[s,t]of[[-1,-1],[1,-1],[1,1],[-1,1]])c.push([cx+ux*a*s+vx*b*t,cz+uz*a*s+vz*b*t]);
   for(let i=0;i<4;i++){const p=c[i],q=c[(i+1)%4],hx=(p[0]+q[0])/2-cx,hz=(p[1]+q[1])/2-cz;q143([p[0],y0,p[1]],[q[0],y0,q[1]],[q[0],y1,q[1]],[p[0],y1,p[1]],[hx,0,hz],col)}
   q143([c[0][0],y1,c[0][1]],[c[1][0],y1,c[1][1]],[c[2][0],y1,c[2][1]],[c[3][0],y1,c[3][1]],[0,1,0],col)}
  function cyl143(cx,cz,y0,y1,r,col){for(let i=0;i<8;i++){const a0=i*Math.PI/4,a1=a0+Math.PI/4,x0=cx+Math.cos(a0)*r,z0=cz+Math.sin(a0)*r,x1=cx+Math.cos(a1)*r,z1=cz+Math.sin(a1)*r;
    q143([x0,y0,z0],[x1,y0,z1],[x1,y1,z1],[x0,y1,z0],[Math.cos(a0+.39),0,Math.sin(a0+.39)],col);tri143(cx,y1+r*.15,cz,x0,y1,z0,x1,y1,z1,0,1,0,col)}}
  const pip143=(P,n,x,z)=>{let c=false;for(let i=0,j=n-1;i<n;j=i++){const zi=P[2*i+1],zj=P[2*j+1];if((zi>z)!=(zj>z)&&x<(P[2*j]-P[2*i])*(z-zi)/(zj-zi)+P[2*i])c=!c}return c};
  const C143={ch:rgb(0xd6cdbd),cap:rgb(0x6d6259),pan:rgb(0x1c2a3c),fr:rgb(0xa9adb1),tk:rgb(0xeeeeea),ci:[rgb(0x2b2b2b),rgb(0x2f5f9a),rgb(0xdedbd2)]};
  function roof143(P,n,top,pit,sb,A){if(A<40||A>1500)return;const r=hs(sb+9.1);let cx=0,cz=0;for(let i=0;i<n;i++){cx+=P[2*i]/n;cz+=P[2*i+1]/n}
   const inside=(x,z,m)=>pip143(P,n,x+m,z+m)&&pip143(P,n,x-m,z+m)&&pip143(P,n,x+m,z-m)&&pip143(P,n,x-m,z-m);
   if(pit&&pit.R){if(r>.6)return;const k=A>180&&r<.22?2:1;for(let c=0;c<k;c++){const t=(c?-.28:.24)*pit.bl,d=pit.d0+(hs(sb+c)-.5)*pit.hw*.6,x=pit.cx+pit.ux*t+pit.vx*d,z=pit.cz+pit.uz*t+pit.vz*d;if(!inside(x,z,.5))continue;
     const yt=top+pit.R+.75,yb=top+pit.R*(1-Math.abs(d-pit.d0)/pit.hw)-.25;box143(x,z,yb,yt,.28,.28,pit.ux,pit.uz,C143.ch);box143(x,z,yt,yt+.09,.38,.38,pit.ux,pit.uz,C143.cap)}return}
   if(r<.3){/* pannello solare termico verso sud con serbatoio orizzontale */const ox=(hs(sb+2)-.5)*Math.sqrt(A)*.3,oz=(hs(sb+3)-.5)*Math.sqrt(A)*.3;let x=cx+ox,z=cz+oz;if(!inside(x,z,1.25)){x=cx;z=cz;if(!inside(x,z,1.25))return}
    const y=top+.06,A1=[x-.55,y+.25,z+.75],B1=[x+.55,y+.25,z+.75],C1=[x+.55,y+1.45,z-.65],D1=[x-.55,y+1.45,z-.65];q143(A1,B1,C1,D1,[0,.7,.7],C143.pan);q143(A1,B1,C1,D1,[0,-.7,-.7],C143.fr);
    box143(x,z-.62,y+1.42,y+1.92,.95,.26,1,0,C143.tk);box143(x-.5,z-.65,y,y+1.42,.04,.04,1,0,C143.fr);box143(x+.5,z-.65,y,y+1.42,.04,.04,1,0,C143.fr);
    if(A>220&&r<.12){const x2=x+1.35;if(inside(x2,z,1.25)){const A2=[x2-.55,y+.25,z+.75],B2=[x2+.55,y+.25,z+.75],C2=[x2+.55,y+1.45,z-.65],D2=[x2-.55,y+1.45,z-.65];q143(A2,B2,C2,D2,[0,.7,.7],C143.pan);box143(x2,z-.62,y+1.42,y+1.92,.95,.26,1,0,C143.tk)}}return}
   if(r<.55){/* cisterna */const x=cx+(hs(sb+5)-.5)*Math.sqrt(A)*.35,z=cz+(hs(sb+6)-.5)*Math.sqrt(A)*.35;if(!inside(x,z,.8))return;cyl143(x,z,top,top+1.25,.6,C143.ci[Math.floor(hs(sb+7)*3)]);
    if(r<.38&&inside(x+1.4,z,.8))cyl143(x+1.4,z,top,top+1.25,.6,C143.ci[Math.floor(hs(sb+8)*3)])}}
  /* v138: campanile delle chiese (lato stretto del lato piu' lungo, dentro la sagoma), tetto a piramide */
  function tower138(P,n,gmin,top,boxes){let cx=0,cz=0,sxx=0,szz=0,sxz=0,ar=0;for(let i=0;i<n;i++){cx+=P[2*i]/n;cz+=P[2*i+1]/n}for(let i=0;i<n;i++){const j=(i+1)%n,dx=P[2*i]-cx,dz=P[2*i+1]-cz;sxx+=dx*dx;szz+=dz*dz;sxz+=dx*dz;ar+=P[2*i]*P[2*j+1]-P[2*j]*P[2*i+1]}if(Math.abs(ar)/2<80)return;
   /* asse principale della sagoma: il campanile va a un capo, rientrato verso il centro */const an=.5*Math.atan2(2*sxz,sxx-szz),ux=Math.cos(an),uz=Math.sin(an),vx=-uz,vz=ux;let pm=-1e9,ex=0,ez=0;for(let i=0;i<n;i++){const pr=(P[2*i]-cx)*ux+(P[2*i+1]-cz)*uz;if(pr>pm){pm=pr;ex=P[2*i];ez=P[2*i+1]}}
   const S=Math.min(5.5,Math.max(3.6,pm*.3)),dl=Math.hypot(cx-ex,cz-ez)||1,hx=ex+(cx-ex)/dl*S*.8,hz=ez+(cz-ez)/dl*S*.8;
   const th=Math.max(top+8,gmin+18),col=rgb(0xd2c3a3),C=[[-1,-1],[1,-1],[1,1],[-1,1]].map(([a,b])=>[hx+(ux*a+vx*b)*S/2,hz+(uz*a+vz*b)*S/2]);
   for(let k=0;k<4;k++){const A=C[k],B=C[(k+1)%4],L=Math.hypot(B[0]-A[0],B[1]-A[1]),nx=(B[1]-A[1])/L,nz=-(B[0]-A[0])/L,o=nx*(A[0]-hx)+nz*(A[1]-hz)>0?1:-1;
    quad(A[0],A[1],B[0],B[1],gmin-.3,gmin-.3,th-3.2,th-3.2,nx*o,nz*o,col,3,7);quad(A[0],A[1],B[0],B[1],th-3.2,th-3.2,th,th,nx*o,nz*o,rgb(0x8a8174),1,7);
    tri138(A[0],th,A[1],B[0],th,B[1],hx,th+S*.9,hz,rgb(0xa9583a))}
   let x0=1e9,x1=-1e9,z0=1e9,z1=-1e9;for(const c of C){x0=Math.min(x0,c[0]);x1=Math.max(x1,c[0]);z0=Math.min(z0,c[1]);z1=Math.max(z1,c[1])}boxes.push(x0,z0,x1,z1,th)}
  /* v128: finestre e balconi per le finestre 3D vicine (FIN127): [x,y,z,nx,nz,w,h,tipo] e [x,y,z,nx,nz,w,parapetto] */
  const WN=[],BN=[],WU=[[[1.6,1,1.15,1.45],[5.7,1,1.15,1.45]],[[1.4,.1,1.1,2.3,1],[5.6,1,1.15,1.45]],[[.9,1,1.05,1.45],[3.7,1,1.05,1.45],[6.5,1,1.05,1.45]],[[1.6,.1,1.1,2.3,1],[5.8,.1,1.1,2.3,1]],
   [[.9,1,1.05,1.45],[3.7,.1,1.1,2.3,1],[6.5,1,1.05,1.45]],[[1.3,.1,1.1,2.3,1],[5.9,.1,1.1,2.3,1]],[[2,1,1.1,1.45],[5.4,1,1.1,1.45]]],
   WG=[[[5,1.05,1.15,1.4]],[],[[1,1.05,1.1,1.4],[6.4,1.05,1.1,1.4]],[],[[3.7,1.05,1.1,1.4]],[],[]],WB=[[],[[.9,2.1]],[],[[.8,6.9]],[[3,2.5]],[[.8,2.1],[5.4,2.1]],[]];
  const win128=(x0,z0,x1,z1,g0,top,fl,nx,nz,v)=>{const L=Math.hypot(x1-x0,z1-z0),dx=(x1-x0)/L,dz=(z1-z0)/L,su=L/8.5,fh=(top-g0)/fl,sv=fh/3.2;if(fh<2.2||fl>12)return;const y0=g0;
   for(let f=0;f<fl;f++){for(const q of(f==0?WG[v]:WU[v])){const tc=(q[0]+q[2]/2)*su,x=x0+dx*tc,z=z0+dz*tc,op=hs(x*3.1+z*7.7+f)<.3?16:0;WN.push(x,y0+f*fh+q[1]*sv,z,nx,nz,q[2]*su,q[3]*sv,v+(q[4]?8:0)+op)}
    if(f==0&&v==3){const tc=2.7*su;WN.push(x0+dx*tc,y0+2.72*sv,z0+dz*tc,nx,nz,4.3*su,.55,32)}
    if(f>0)for(const b of WB[v]){const tc=(b[0]+b[1]/2)*su;BN.push(x0+dx*tc,y0+f*fh,z0+dz*tc,nx,nz,(b[1]+.3)*su,v%2)}}};
  let bi=0;
  for(const b of d.b){bi++;const H=b[0]/10,rc=b[1],fl=b[2],sp=fl&7,n=b[3],P=[];for(let k=0;k<n;k++)P.push(ox+b[4+2*k]/10,oz+b[5+2*k]/10);if(exz(P[0],P[1]))continue;
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
   let rcol=rgb(rc||0xb8b2a6);rcol=rcol.map(c=>Math.min(1,c*1.08));
   /* v138: tetto a due falde dove la foto mostra le tegole (colore cotto) e sulle chiese; chiese col campanile */
   const rr=rc>>16&255,rg=rc>>8&255,rb=rc&255,cotto=rc&&rr-rb>55&&rr-rg>25,wcol=base||rgb(PAL[Math.floor(hs(sb)*PAL.length)]);
   let pit=0;if((cotto&&sp==0&&H<=16&&Math.abs(ar)/2<900)||sp==1){if(sp==1)rcol=rgb(0xb0623f);pit=roof138(P,n,top,rcol,wcol,sp==1?.55:.42,sp==1?7:3.2)}
   if(sp==1)tower138(P,n,gmin,top,boxes);
   if(lod&&sp==0&&H<=22)roof143(P,n,top,pit,sb,Math.abs(ar)/2);
   if(!pit){const tr=ear(P);
   for(let q=0;q<tr.length;q+=3)for(const t of[tr[q],tr[q+2],tr[q+1]]){RF.p.push(P[2*t],top,P[2*t+1]);RF.n.push(0,1,0);RF.u.push(0,0);RF.c.push(...rcol)}}
   // muretto in cima ai palazzi alti (parapetto)
   if(H>8&&sp==0&&lod&&!pit){for(let i=0;i<n;i++){const j=(i+1)%n,ax=P[2*i],az=P[2*i+1],bx=P[2*j],bz=P[2*j+1],L=Math.hypot(bx-ax,bz-az);if(L<.5)continue;const nx=(bz-az)/L,nz=-(bx-ax)/L;quad(ax,az,bx,bz,top,top,top+.9,top+.9,nx,nz,rgb(0xe9e5dc),3,7)}}
   // urti: strisce di 3 m lungo z
   let zmin=1e9,zmax=-1e9;for(let i=0;i<n;i++){zmin=Math.min(zmin,P[2*i+1]);zmax=Math.max(zmax,P[2*i+1])}
   for(let zc=zmin+1.5;zc<zmax+1.4;zc+=3){const zz=Math.min(zc,zmax-.01),xs=[];for(let i=0;i<n;i++){const j=(i+1)%n,az=P[2*i+1],bz=P[2*j+1];if((az<=zz)!=(bz<=zz)){xs.push(P[2*i]+(zz-az)/(bz-az)*(P[2*j]-P[2*i]))}}xs.sort((a,b)=>a-b);for(let k=0;k+1<xs.length;k+=2)if(xs[k+1]-xs[k]>.3)boxes.push(xs[k],zz-1.5,xs[k+1],zz+1.5,top)}}
  out.walls=W.f();out.roofs=RF.f();out.boxes=new Float32Array(boxes);out.win=new Float32Array(WN);out.bal=new Float32Array(BN);
  // --- alberi ---
  const tr=[],tstep=2;/* v135: stessi alberi anche nei quadrati lontani (prima 1 su 3: avvicinandosi 'spuntavano' gli altri) */for(let k=0;k+1<d.t.length;k+=tstep){const x=ox+d.t[k]/10,z=oz+d.t[k+1]/10;tr.push(x,ht(x,z),z,.8+hs(x*3.1+z)*.7)}out.trees=new Float32Array(tr);/* v135: cespugli (macchia e giardini) */const bu=[];if(d.u)for(let k=0;k+1<d.u.length;k+=lod?2:4){const x=ox+d.u[k]/10,z=oz+d.u[k+1]/10,s=.6+hs(x*1.7+z*.3)*.9;bu.push(x,ht(x,z)+.4*s,z,s)}out.bush=new Float32Array(bu);
  return out}
 /* v149: strade dei quadrati accanto (stesso pacchetto, o pacchetti gia' scaricati) per incroci e marciapiedi */
 const BR=new Map();
 const nbRoads=(BD,key,bs)=>{const[i,j]=key.split('_').map(Number),o=[],B=bs||4;for(let a=-1;a<=1;a++)for(let b=-1;b<=1;b++){if(!a&&!b)continue;const k2=(i+a)+'_'+(j+b),src=BD[k2]?BD:BR.get(Math.floor((i+a)/B)+'_'+Math.floor((j+b)/B)),t=src&&src[k2];if(t&&t.r&&t.r.length)o.push({o:t.o,r:t.r})}return o};
 self.onmessage=async e=>{const m=e.data;
  if(m.t=='init'){Q=m.Q;QH=m.QH;postMessage({t:'ok'});return}
  if(m.t=='tile'){try{const [i,j]=m.key.split('_').map(Number),bk=Math.floor(i/m.bs)+'_'+Math.floor(j/m.bs);
    let pr=BC.get(bk);if(!pr){/* v137: se il secondo sito non risponde, riserva sul sito del gioco (m.u2) */const F2=u=>fetch(m.url+u).then(r=>{if(!r.ok)throw 0;return r}).catch(e=>m.u2&&m.u2!=m.url?fetch(m.u2+u):Promise.reject(e));pr=F2('b_'+bk+'.json').then(r=>r.json());BC.set(bk,pr);if(BC.size>10)BC.delete(BC.keys().next().value)}
    const BD=await pr;if(BD._q&&!FQ.has(bk)){FQ.set(bk,decQ(BD._q));FB=BD._q.fb||2000;while(FQ.size>120)FQ.delete(FQ.keys().next().value)}
    BR.set(bk,BD);if(BR.size>12)BR.delete(BR.keys().next().value);
    const d=Object.assign({},BD[m.key]);d.key=m.key;d.core=m.core;d.ex=m.ex;d.nb=nbRoads(BD,m.key,m.bs);
    let img=null;/* v137: foto del quadrato in un file .jpg a parte (mondo/img/t_I_J.jpg) */if(m.h18){try{const r=await fetch(m.h18);if(r.ok)img=await createImageBitmap(await r.blob())}catch(er){}}if(d.im&&!img){try{const r=await fetch(m.url+'img/t_'+m.key+'.jpg').then(r=>r.ok||!m.u2||m.u2==m.url?r:fetch(m.u2+'img/t_'+m.key+'.jpg'),()=>m.u2?fetch(m.u2+'img/t_'+m.key+'.jpg'):null);if(r.ok)img=await createImageBitmap(await r.blob())}catch(er){}}if(d.img){try{const bs=atob(d.img),u8=new Uint8Array(bs.length);for(let q=0;q<bs.length;q++)u8[q]=bs.charCodeAt(q);img=await createImageBitmap(new Blob([u8],{type:'image/jpeg'}))}catch(er){}}delete d.img;
    const o=build(d,m.lod);o.img=img;o.data=d;if(BD._q){o.q=BD._q;o.bk=bk}const tf=[];for(const k of['ground','water','road','walls','roofs'])if(o[k])for(const a of Object.values(o[k]))tf.push(a.buffer);tf.push(o.boxes.buffer,o.trees.buffer,o.win.buffer,o.bal.buffer,o.bush.buffer,o.sig.buffer);if(img)tf.push(img);
    postMessage(o,tf)}catch(er){postMessage({key:m.key,err:String(er)})}}
  if(m.t=='lod'){try{const o=build(Object.assign({},m.d,{g:0}),m.lod);const tf=[];for(const k of['road','walls','roofs'])for(const a of Object.values(o[k]))tf.push(a.buffer);tf.push(o.boxes.buffer,o.trees.buffer,o.win.buffer,o.bal.buffer,o.bush.buffer,o.sig.buffer);delete o.ground;delete o.water;o.relod=1;postMessage(o,tf)}catch(er){postMessage({key:m.key,err:String(er)})}}};