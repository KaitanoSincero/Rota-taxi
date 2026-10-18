import {initializeApp} from "https://www.gstatic.com/firebasejs/10.7.1/firebase-app.js";
import {getAuth,onAuthStateChanged,signInAnonymously,signInWithEmailAndPassword,createUserWithEmailAndPassword,signOut} from "https://www.gstatic.com/firebasejs/10.7.1/firebase-auth.js";
import {getFirestore,doc,collection,setDoc,updateDoc,getDoc,deleteDoc,onSnapshot,serverTimestamp,Timestamp} from "https://www.gstatic.com/firebasejs/10.7.1/firebase-firestore.js";
import CFG from "./config.js";

const OK=["apiKey","projectId","appId"].every(k=>CFG[k]&&!String(CFG[k]).startsWith("COLAR"));
let auth,db;if(OK){const app=initializeApp(CFG);auth=getAuth(app);db=getFirestore(app)}
const NOW=()=>Date.now(),STALE_POS=90e3,STALE_OCC=120e3,COL={g:"#12805c",y:"#b86e00",r:"#c0302b",u:"#5b6678"};
const $=id=>document.getElementById(id);
const esc=s=>String(s).replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const r4=x=>Math.round(x*1e4)/1e4,r5=x=>Math.round(x*1e5)/1e5,M=111320,SPEED=250; // 250 m/min = 15 km/h; estimativa urbana conservadora
const S={mode:"start",dest:null,sel:null,live:[],routes:[],ready:false,upos:null,me:null,prof:null,appr:null,adm:false,reg:false,err:"",
 chat:[],step:0,de:"",pa:"",rt:null,opts:[],cap:15,occ:0,svc:false,pos:null,posT:0,msg:"",net:"",fit:false,prev:{},geo:{},gm:"",range:2,lastPush:0,rid:null,drv:[],apprIds:new Set()};
let unsub=null,subR=null,subA=null,watchId=null,tick=null,wl=null,map=null,layer=null,bgId=null;
// Na app Android (Capacitor) a localização em segundo plano vem do plugin; no navegador usa-se o GPS normal.
const CAP=window.Capacitor,BG=(CAP&&CAP.isNativePlatform&&CAP.isNativePlatform())?CAP.registerPlugin("BackgroundGeolocation"):null;

const ms=t=>t&&t.toMillis?t.toMillis():NOW();
const age=d=>NOW()-ms(d.t),ageO=d=>NOW()-ms(d.to);
function km(a,b,c,d){const R=6371,p=Math.PI/180,x=Math.sin((c-a)*p/2)**2+Math.cos(a*p)*Math.cos(c*p)*Math.sin((d-b)*p/2)**2;return 2*R*Math.asin(Math.sqrt(x))}
function lot(cap,occ,a){const free=cap-occ;let c="g",tx="Lugares livres";if(free<=0){c="r";tx="Cheio"}else if(free<=Math.ceil(cap*.25)){c="y";tx="Poucos lugares"}if(a>STALE_OCC){c="u";tx="Lotação desconhecida"}return{c,tx,free,old:a>STALE_OCC}}
const tag=l=>`<span class="tag ${l.c}">${l.tx}${l.old?"":" · "+l.free+" livres"}</span>`;
// Rotas iniciais (da v3): nomes sem percurso. Os pontos de partida vêm do GPS dos motoristas. Validar com taxistas.
const ROUTES=[["Benfica","Golf 2",-8.870,13.210],["Rangel","Mutamba",-8.820,13.250],["Viana","Largo do Ambiente",-8.900,13.370],["Cacuaco","Sambizanga",-8.770,13.260],["Palanca","Rocha Pinto",-8.850,13.230],["Cazenga","Maianga",-8.810,13.280],["Kilamba","Camama",-8.980,13.260],["Talatona","Centro",-8.920,13.200]].map(([de,para,la,lo],i)=>({id:"r"+(i+1),de,para,start:[la,lo]}));
const act=()=>ROUTES;
// Direcção relativa ao passageiro: compara a distância entre actualizações (heurística, pode errar em curvas).
function track(){if(!S.upos)return;S.live.forEach(d=>{const k=km(S.upos[0],S.upos[1],d.lat,d.lng),p=S.prev[d.id];if(!p)S.prev[d.id]={k,dir:"?"};else if(Math.abs(k-p.k)>.02)S.prev[d.id]={k,dir:k<p.k?"in":"out"}})}
const fmt=m=>m>=1000?(m/1000).toFixed(1).replace(".",",")+" km":Math.round(m)+" m";

/* ---------- Ligação ---------- */
function subLive(){if(unsub||!OK)return;unsub=onSnapshot(collection(db,"live"),snap=>{S.live=snap.docs.map(d=>({id:d.id,...d.data()}));S.ready=true;S.err="";track();render()},e=>{S.err="Erro a ler os táxis ("+e.code+").";render()})}
function mk(g){const n=g.la.length,k=111320*Math.cos(g.la[0]*Math.PI/180),xy=g.la.map((la,i)=>[g.lo[i]*k,la*111320]),c=[0];
 for(let i=1;i<n;i++)c.push(c[i-1]+Math.hypot(xy[i][0]-xy[i-1][0],xy[i][1]-xy[i-1][1]));return{xy,c,k,len:c[n-1],km:g.km}}
// Projecta um ponto no percurso: distância ao longo da rota, desvio (m) e ponto mais próximo.
function proj(G,lat,lng){const p=[lng*G.k,lat*111320];let b=null;
 for(let i=0;i<G.xy.length-1;i++){const A=G.xy[i],B=G.xy[i+1],dx=B[0]-A[0],dy=B[1]-A[1],L2=dx*dx+dy*dy||1;let t=((p[0]-A[0])*dx+(p[1]-A[1])*dy)/L2;t=Math.max(0,Math.min(1,t));
  const x=A[0]+t*dx,y=A[1]+t*dy,off=Math.hypot(p[0]-x,p[1]-y);if(!b||off<b.off)b={off,along:G.c[i]+t*Math.sqrt(L2),x,y}}return b}
function etaOf(d){const G=S.geo[d.rid],u=S.upos;if(!G)return null;if(!u)return{t:"activa a localização para ver o tempo"};
 const pu=proj(G,u[0],u[1]);if(pu.off>800)return{t:"esta rota não passa perto de ti",o:1};
 const pt=proj(G,d.lat,d.lng);if(pt.off>300)return{t:"fora do percurso",o:1};const gap=pu.along-pt.along;
 if(gap<-40)return{t:"já passou por ti",o:1};return{t:`~${Math.max(1,Math.round(gap/SPEED))} min · ${fmt(Math.max(0,gap))}`,g:Math.max(0,gap),ok:1}}
function subRoutes(){if(subR||!OK)return;subR=onSnapshot(collection(db,"routes"),snap=>{const g={};snap.docs.forEach(d=>{const x=d.data();if(Array.isArray(x.la)&&Array.isArray(x.lo)&&x.la.length>=2&&x.la.length==x.lo.length)g[d.id]=mk(x)});S.geo=g;render()},e=>{S.err="Erro a ler as rotas ("+e.code+").";render()})}
function subAdmin(){if(subA||!S.adm)return;subA=[onSnapshot(collection(db,"drivers"),x=>{S.drv=x.docs.map(d=>({id:d.id,...d.data()}));render()},()=>{}),onSnapshot(collection(db,"approved"),x=>{S.apprIds=new Set(x.docs.map(d=>d.id));render()},()=>{})]}
async function openPassenger(){
 if(!OK)return;
 try{if(!auth.currentUser)await signInAnonymously(auth)}catch(e){S.err="Não foi possível entrar. Verifica a internet e se o login anónimo está activo no Firebase.";render();return}
 subLive();subRoutes();
 if(navigator.geolocation&&!S.upos)navigator.geolocation.getCurrentPosition(p=>{S.upos=[p.coords.latitude,p.coords.longitude];track();render()},()=>{},{maximumAge:60000,timeout:8000});
}
if(OK)onAuthStateChanged(auth,async u=>{
 [unsub,subR].forEach(f=>f&&f());unsub=subR=null;S.geo={};(subA||[]).forEach(f=>f());subA=null;
 S.me=u;S.appr=null;S.prof=null;S.adm=false;S.live=[];S.routes=[];S.ready=false;
 if(u){subRoutes();if(S.mode=="p")subLive()}
 if(u&&!u.isAnonymous){try{const[p,a,ad]=await Promise.all([getDoc(doc(db,"drivers",u.uid)),getDoc(doc(db,"approved",u.uid)),getDoc(doc(db,"admins",u.uid))]);S.prof=p.exists()?p.data():null;S.appr=a.exists();S.adm=ad.exists();if(S.adm)subAdmin()}catch(e){S.err="Erro ao verificar a conta ("+e.code+").";S.appr=false}}
 render()});

/* ---------- Ecrãs ---------- */
const setup=()=>`<div class="card"><h2>Falta ligar ao Firebase</h2><p>Abre o ficheiro <b>config.js</b> e cola a configuração da tua app Web do Firebase. Os passos estão no <b>LEIA-ME.md</b>.</p></div>`;
function start(){return`<div class="start"><h2 style="font-size:1.4rem">Como vais usar o Rota Táxi?</h2>
<button class="big pas" data-m="p">Sou passageiro<small>Diz para onde vais e vê os táxis a chegar</small></button>
<button class="big mot" data-m="t">Sou motorista<small>Define a tua rota e partilha a lotação</small></button>
<button class="btn" data-m="a" style="align-self:center;margin-top:10px;min-height:36px;font-weight:500">Administração</button></div>`}

function routeSvg(G,rt,rows){
 const u=S.upos,W=360,H=320,pad=34,pts=G.xy.slice(),tx=rows.filter(r=>r.d.rid==rt.id);
 tx.forEach(r=>pts.push([r.d.lng*G.k,r.d.lat*111320]));
 let pu=null;if(u){pu=proj(G,u[0],u[1]);if(pu.off<=800)pts.push([pu.x,pu.y]);else pu=null}
 const xs=pts.map(p=>p[0]),ys=pts.map(p=>p[1]),x0=Math.min(...xs),x1=Math.max(...xs),y0=Math.min(...ys),y1=Math.max(...ys);
 const sc=Math.min((W-2*pad)/((x1-x0)||1),(H-2*pad)/((y1-y0)||1)),X=x=>(W-(x1-x0)*sc)/2+(x-x0)*sc,Y=y=>(H-(y1-y0)*sc)/2+(y1-y)*sc;
 let h=`<svg class="map" viewBox="0 0 ${W} ${H}" role="img" aria-label="Esquema da rota"><polyline points="${G.xy.map(p=>X(p[0]).toFixed(1)+","+Y(p[1]).toFixed(1)).join(" ")}" fill="none" stroke="var(--pri)" stroke-width="6" stroke-linecap="round" stroke-linejoin="round" opacity=".4"/>
 <text x="12" y="${H-10}" font-size="11" fill="var(--mu)">${esc(rt.de)} → ${esc(rt.para)}</text>`;
 if(pu)h+=`<g transform="translate(${X(pu.x).toFixed(1)},${Y(pu.y).toFixed(1)})"><circle r="11" fill="var(--sf)" stroke="var(--tx)" stroke-width="3"/><text y="4" text-anchor="middle" font-size="12" font-weight="700" fill="var(--tx)">P</text></g>`;
 tx.forEach(({d,l,e,dir})=>{let x=d.lng*G.k,y=d.lat*111320;const p=proj(G,d.lat,d.lng);if(p.off<=150){x=p.x;y=p.y}
  h+=`<g data-t="${esc(d.id)}" transform="translate(${X(x).toFixed(1)},${Y(y).toFixed(1)})" style="cursor:pointer" opacity="${(e&&e.o)||dir=="out"?.55:1}"><circle r="22" fill="transparent"/><rect x="-14" y="-10" width="28" height="20" rx="6" fill="${COL[l.c]}" stroke="${S.sel==d.id?"var(--ac)":"var(--sf)"}" stroke-width="3"/><rect x="-9" y="-5" width="18" height="5" rx="1.5" fill="var(--sf)" opacity=".85"/></g>`});
 return h+`</svg><p class="mu">Percurso calculado a partir do mapa livre (estimado). P = ponto da rota mais perto de ti. Cor do táxi: verde lugares · amarelo poucos · vermelho cheio · cinza desconhecida.</p>`}
function radarSvg(rows){
 const u=S.upos,R=S.range*1000,c=180,P=160,kx=111320*Math.cos(u[0]*Math.PI/180);let out=0;
 let h=`<div class="row" style="margin-bottom:10px">${[1,2,3].map(n=>`<button class="chip" aria-pressed="${S.range==n}" data-rg="${n}">${n} km</button>`).join("")}</div><svg class="map" viewBox="0 0 360 360" role="img" aria-label="Táxis à tua volta">`;
 [1/3,2/3,1].forEach(f=>h+=`<circle cx="${c}" cy="${c}" r="${P*f}" fill="none" stroke="var(--mu)" stroke-opacity=".35" stroke-dasharray="4 6"/><text x="${c}" y="${c-P*f-4}" text-anchor="middle" font-size="10" fill="var(--mu)">${fmt(R*f)}</text>`);
 h+=`<text x="12" y="20" font-size="11" fill="var(--mu)">N ↑</text>`;
 rows.forEach(({d,m,dir,l})=>{if(m>R){out++;return}const x=c+(d.lng-u[1])*kx/R*P,y=c-(d.lat-u[0])*111320/R*P;
  h+=`<g data-t="${esc(d.id)}" transform="translate(${x.toFixed(1)},${y.toFixed(1)})" style="cursor:pointer" opacity="${dir=="out"?.55:1}"><circle r="22" fill="transparent"/><rect x="-14" y="-10" width="28" height="20" rx="6" fill="${COL[l.c]}" stroke="${S.sel==d.id?"var(--ac)":"var(--sf)"}" stroke-width="3"/><rect x="-9" y="-5" width="18" height="5" rx="1.5" fill="var(--sf)" opacity=".85"/></g>`});
 return h+`<circle cx="${c}" cy="${c}" r="9" fill="var(--pri)" stroke="#fff" stroke-width="3"/><text x="${c}" y="${c+26}" text-anchor="middle" font-size="12" font-weight="700" fill="var(--tx)">Tu</text></svg><p class="mu">Sem percurso calculado para esta rota: mostro os táxis à tua volta (norte para cima).${out?` ${out} fora do alcance de ${S.range} km.`:""}</p>`}
function passenger(){
 if(!OK)return setup();
 const fresh=S.live.filter(d=>age(d)<=STALE_POS),err=S.err?`<p class="err">${esc(S.err)}</p>`:"";
 if(!S.dest){
  const cnt={};fresh.forEach(d=>cnt[d.para]=(cnt[d.para]||0)+1);
  const all=[...new Set(ROUTES.map(r=>r.para))].sort((a,b)=>(cnt[b]||0)-(cnt[a]||0)||a.localeCompare(b,"pt"));
  return err+`<h2 style="font-size:1.3rem;margin-top:8px">Para onde vais?</h2><p class="mu">Escolhe o destino final.</p>`+all.map(p=>`<button class="item" data-dest="${esc(p)}" style="font-size:1.1rem"><b>${esc(p)}</b><span class="${cnt[p]?"g":"mu"}">${cnt[p]?cnt[p]+" táxi(s)":"nenhum agora"}</span></button>`).join("")}
 const all=S.live.filter(d=>d.para==S.dest),vis=all.filter(d=>age(d)<=STALE_POS),old=all.length-vis.length,u=S.upos;
 const score=x=>x.e?(x.e.ok?x.e.g:1e8):(x.dir=="out"?1e8+(x.m||0):(x.m??9e7));
 const rows=vis.map(d=>{const p=S.prev[d.id];return{d,m:u?km(u[0],u[1],d.lat,d.lng)*1000:null,dir:p?p.dir:"?",l:lot(d.cap,d.occ,ageO(d)),e:etaOf(d)}}).sort((a,b)=>score(a)-score(b));
 const rt=ROUTES.find(r=>r.para==S.dest),G=rt&&S.geo[rt.id];let h=err;
 if(G)h+=routeSvg(G,rt,rows);
 else if(u)h+=radarSvg(rows);
 else h+=`<div class="card"><b>Sem a tua localização</b><p class="mu">Permite a localização no navegador para ver os táxis à tua volta.</p></div>`;
 h+=u?`<button class="chip" data-loc="1" style="margin-bottom:10px">Actualizar a minha posição</button>`:`<button class="btn p" data-loc="1" style="width:100%;margin-bottom:10px">Activar a minha localização</button>`;
 h+=`<h2 style="margin-top:6px">Táxis para ${esc(S.dest)}</h2>`;
 if(!rows.length)h+=`<div class="card mu">Nenhum táxi para ${esc(S.dest)} com posição actual neste momento.</div>`;
 const dt={in:"a aproximar-se",out:"a afastar-se","?":"a calcular direcção"};
 rows.forEach(({d,m,dir,l,e})=>h+=`<button class="item" data-t="${esc(d.id)}" style="${(e&&e.o)||(!e&&dir=="out")?"opacity:.6":""}"><span><b>${esc(d.veic||"Táxi")}</b><br><span class="mu">vem de ${esc(d.de)} · ${e?esc(e.t):(m==null?"":fmt(m)+" · ")+dt[dir]}</span></span><span style="text-align:right">${tag(l)}</span></button>`);
 if(old)h+=`<p class="mu">${old} táxi(s) escondido(s): sem sinal há mais de 90 s.</p>`;
 const t=S.sel&&all.find(x=>x.id==S.sel);
 if(t){const l=lot(t.cap,t.occ,ageO(t));h+=`<div class="card" style="border-color:var(--pri)"><h2>${esc(t.veic||"Táxi")}</h2><div>Rota: ${esc(t.de)} → ${esc(t.para)}</div><div>${tag(l)}</div><div class="mu">Posição: há ${Math.round(age(t)/1000)} s · lotação: há ${Math.round(ageO(t)/1000)} s · posição aproximada (cerca de 10 m). Tempo estimado a 15 km/h.</div><button class="btn" data-x="1" style="margin-top:8px">Fechar</button></div>`}
 return h}

/* ---------- Motorista ---------- */
// Percurso: coordenadas dos dois locais (Nominatim) + rota por estrada (OSRM), ambos do mapa livre OpenStreetMap.
// Calcula-se uma vez por rota e guarda-se no Firestore; os passageiros só leem.
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
async function geocode(q){const r=await fetch("https://nominatim.openstreetmap.org/search?format=jsonv2&limit=1&countrycodes=ao&viewbox=12.8,-8.3,14.0,-9.6&bounded=1&q="+encodeURIComponent(q+", Luanda"),{headers:{"Accept-Language":"pt"}});
 if(!r.ok)throw new Error("geo");const j=await r.json();if(!j[0])throw new Error("geo0");return[+j[0].lat,+j[0].lon]}
function dp(p,tol){const n=p.length,keep=new Uint8Array(n);keep[0]=keep[n-1]=1;const st=[[0,n-1]];
 while(st.length){const[s,e]=st.pop(),A=p[s],B=p[e],dx=B[0]-A[0],dy=B[1]-A[1],L2=dx*dx+dy*dy||1;let md=0,mi=-1;
  for(let i=s+1;i<e;i++){let t=((p[i][0]-A[0])*dx+(p[i][1]-A[1])*dy)/L2;t=Math.max(0,Math.min(1,t));const d=Math.hypot(p[i][0]-A[0]-t*dx,p[i][1]-A[1]-t*dy);if(d>md){md=d;mi=i}}
  if(md>tol&&mi>0){keep[mi]=1;st.push([s,mi],[mi,e])}}
 return[...keep].map((k,i)=>k?i:-1).filter(i=>i>=0)}
async function ensureRoute(r){
 if(!r||!OK||S.geo[r.id])return;S.gm="A calcular o percurso no mapa livre…";render();
 try{let a;try{a=await geocode(r.de)}catch(e){a=r.start}await sleep(1100);const b=await geocode(r.para);
  const j=await(await fetch(`https://router.project-osrm.org/route/v1/driving/${a[1]},${a[0]};${b[1]},${b[0]}?overview=full&geometries=geojson`)).json();
  if(j.code!="Ok")throw new Error("osrm");const c=j.routes[0].geometry.coordinates,kx=111320*Math.cos(a[0]*Math.PI/180),p=c.map(([lo,la])=>[lo*kx,la*111320]);
  let tol=10,keep;do{keep=dp(p,tol);tol*=1.6}while(keep.length>180);
  await setDoc(doc(db,"routes",r.id),{de:r.de,para:r.para,la:keep.map(i=>r5(c[i][1])),lo:keep.map(i=>r5(c[i][0])),km:Math.round(j.routes[0].distance/100)/10,t:serverTimestamp()});
  S.gm="Percurso calculado e guardado."}
 catch(e){S.gm=S.geo[r.id]?"":"Não foi possível calcular o percurso agora. Segues na mesma: os passageiros veem-te sem a linha da rota."}
 render()}

const say=t=>S.chat.push({w:"a",t}),me=t=>S.chat.push({w:"u",t});
function lastRid(){try{const v=localStorage.getItem("rt_last2");return act().find(r=>r.id==v)||null}catch(e){return null}}
const og=()=>[...new Set(act().map(r=>r.de))],dl=()=>act().filter(r=>r.de==S.de);
function driverInit(){S.chat=[];S.step=0;S.msg="";S.rt=null;say("Bom dia! Bem-vindo ao Rota Táxi.");say("De onde sais hoje?")}
function toConfirm(r){S.rt=r.id;S.de=r.de;S.pa=r.para;say(`Encontrei a rota ${r.de} → ${r.para}. É esta a rota de hoje?`);S.step=2;S.opts=[{k:"y",l:"Sim, é esta"},{k:"n",l:"Não, mudar de rota"}]}
async function answer(k){
 if(k=="L"){const r=lastRid();me(`${r.de} → ${r.para}`);toConfirm(r)}
 else if(k[0]=="o"){S.de=og()[+k.slice(1)];me(S.de);say("Para onde vais?");S.step=1}
 else if(k[0]=="d"){const r=dl()[+k.slice(1)];me(r.para);toConfirm(r)}
 else if(k=="n"){me("Não, mudar de rota");say("Sem problema. De onde sais hoje?");S.step=0}
 else if(k=="y"){me("Sim, é esta");try{localStorage.setItem("rt_last2",S.rt)}catch(e){}say("Quantos lugares tem o teu táxi?");S.step=3;S.opts=[12,14,15,18].map(n=>({k:"c"+n,l:n+" lugares"}));ensureRoute(ROUTES.find(x=>x.id==S.rt))}
 else if(k[0]=="c"){S.cap=+k.slice(1);me(S.cap+" lugares");say("Posso activar a localização? A posição do táxi (aproximada, cerca de 10 m) fica visível aos passageiros até terminares o serviço.");S.step=4;S.opts=[{k:"go",l:"Activar localização"},{k:"no",l:"Agora não"}]}
 else if(k=="no"){me("Agora não");say("Tudo bem. Só começo a partilhar quando disseres.")}
 else if(k=="go"){me("Activar localização");render();await startSvc()}}
function getPos(){return new Promise(res=>navigator.geolocation?navigator.geolocation.getCurrentPosition(p=>res(p),e=>res(e),{enableHighAccuracy:true,timeout:15000}):res({code:0}))}
async function startSvc(){
 const p=await getPos();
 if(!p.coords){say(p.code==1?"Sem permissão de localização. Activa-a nas definições do navegador e tenta de novo.":"Não consegui obter o GPS. Vai para um local aberto e tenta de novo.");S.opts=[{k:"go",l:"Tentar de novo"}];render();return}
 S.pos=p;S.posT=NOW();S.occ=0;
 try{await setDoc(doc(db,"live",S.me.uid),{rid:S.rt,de:S.de,para:S.pa,cap:S.cap,occ:0,veic:S.prof.matricula,lat:r4(p.coords.latitude),lng:r4(p.coords.longitude),t:serverTimestamp(),to:serverTimestamp(),exp:Timestamp.fromMillis(NOW()+6e5)})}
 catch(e){say("Não consegui iniciar ("+e.code+"). Confirma a internet, a aprovação da conta e se a rota continua activa.");S.opts=[{k:"go",l:"Tentar de novo"}];render();return}
 S.svc=true;S.step=5;S.opts=[];S.msg="Serviço iniciado. Mantém a aplicação aberta e o ecrã ligado. No navegador a localização em segundo plano não é garantida; na app Android sim.";
 if(BG){try{bgId=await BG.addWatcher({backgroundTitle:"Rota Táxi em serviço",backgroundMessage:"A partilhar a posição do táxi com os passageiros.",requestPermissions:true,stale:false,distanceFilter:0},(l,e)=>{
  if(e){S.err=e.code=="NOT_AUTHORIZED"?"Sem permissão de localização. Permite a localização «sempre» nas definições.":"Erro de GPS.";if(e.code=="NOT_AUTHORIZED")BG.openSettings();render();return}
  S.pos={coords:{latitude:l.latitude,longitude:l.longitude}};S.posT=NOW();if(NOW()-S.lastPush>12e3)push()})}catch(e){S.err="Não foi possível iniciar o GPS em segundo plano."}}
 else watchId=navigator.geolocation.watchPosition(q=>{S.pos=q;S.posT=NOW()},()=>{},{enableHighAccuracy:true,maximumAge:5000});
 tick=setInterval(()=>push(),15000);wlock();render()}
async function push(extra={}){
 if(!S.svc)return;S.lastPush=NOW();
 const freshPos=!!(S.pos&&NOW()-S.posT<45e3);
 const d={exp:Timestamp.fromMillis(NOW()+6e5),...extra};
 if(freshPos){
  d.lat=r4(S.pos.coords.latitude);d.lng=r4(S.pos.coords.longitude);d.t=serverTimestamp();S.err="";
 }else if(Object.prototype.hasOwnProperty.call(extra,"occ")){
  // A lotação pode ser actualizada sem fingir que a posição GPS também é recente.
  d.to=serverTimestamp();S.err="Sem sinal de GPS há mais de 45 s: a posição ficará desactualizada até o GPS voltar.";
 }else{
  S.err="Sem sinal de GPS há mais de 45 s: a posição não foi actualizada.";render();return;
 }
 try{await updateDoc(doc(db,"live",S.me.uid),d);S.net=(freshPos?"Posição enviada às ":"Lotação enviada às ")+new Date().toLocaleTimeString("pt",{hour:"2-digit",minute:"2-digit"})}catch(e){S.net="Erro a enviar ("+e.code+")"}
 render()}
function setOcc(n,txt){S.occ=Math.max(0,Math.min(S.cap,n));const f=S.cap-S.occ;S.msg=txt+(f==0?" Táxi cheio: os passageiros veem vermelho.":` Agora há ${f} lugar(es) livre(s).`);push({occ:S.occ,to:serverTimestamp()})}
async function endSvc(){clearInterval(tick);if(bgId){try{BG.removeWatcher({id:bgId})}catch(e){}bgId=null}if(watchId!=null)navigator.geolocation.clearWatch(watchId);watchId=null;try{if(wl)wl.release()}catch(e){}
 const was=S.svc;S.svc=false;if(was&&S.me)try{await deleteDoc(doc(db,"live",S.me.uid))}catch(e){}driverInit()}
async function wlock(){try{if("wakeLock"in navigator)wl=await navigator.wakeLock.request("screen")}catch(e){}}
document.addEventListener("visibilitychange",()=>{if(document.visibilityState=="visible"&&S.svc)wlock()});

const AERR={"auth/invalid-credential":"Email ou palavra-passe errados.","auth/email-already-in-use":"Esse email já tem conta.","auth/weak-password":"Palavra-passe fraca (mínimo 6 caracteres).","auth/invalid-email":"Email inválido.","auth/network-request-failed":"Sem internet."};
async function doAuth(){
 const em=$("em").value.trim(),pw=$("pw").value;S.err="";
 try{
  if(!(S.reg&&S.mode=="t"))await signInWithEmailAndPassword(auth,em,pw);
  else{const nome=$("nm").value.trim(),tel=$("tl").value.replace(/\D/g,""),mat=$("mt").value.trim().toUpperCase();
   if(nome.length<2||nome.length>60)throw{code:"x",m:"Escreve o teu nome."};if(tel.length<7||tel.length>15)throw{code:"x",m:"Telefone inválido."};if(!/^[A-Z0-9-]{3,12}$/.test(mat))throw{code:"x",m:"Matrícula inválida."};
   const c=await createUserWithEmailAndPassword(auth,em,pw);
   await setDoc(doc(db,"drivers",c.user.uid),{nome,telefone:tel,matricula:mat,criado:serverTimestamp()});}
 }catch(e){S.err=e.m||AERR[e.code]||"Erro ("+(e.code||"?")+").";render()}}
function login(canReg){const r=S.reg&&canReg;return`<div class="card"><h2>${r?"Criar conta de motorista":canReg?"Entrar como motorista":"Entrar como administrador"}</h2>${S.err?`<div class="err">${esc(S.err)}</div>`:""}
${r?`<label for="nm">Nome</label><input id="nm" class="f" maxlength="60" autocomplete="name"><label for="tl">Telefone</label><input id="tl" class="f" inputmode="tel" maxlength="20" autocomplete="tel"><label for="mt">Matrícula</label><input id="mt" class="f" maxlength="12" autocapitalize="characters">`:""}
<label for="em">Email</label><input id="em" class="f" type="email" autocomplete="email"><label for="pw">Palavra-passe</label><input id="pw" class="f" type="password" autocomplete="${r?"new-password":"current-password"}">
<button class="btn p" data-auth="1" style="width:100%;min-height:52px">${r?"Criar conta":"Entrar"}</button>${canReg?`<button class="btn" data-reg="1" style="width:100%;margin-top:8px">${r?"Já tenho conta":"Criar conta nova"}</button>`:""}</div>
${canReg?`<p class="mu">O telefone e o email só são vistos por ti e pelo administrador. Os passageiros veem apenas a matrícula, a rota, a posição aproximada e a lotação.</p>`:""}`}
function taxista(){
 if(!OK)return setup();
 if(!S.me||S.me.isAnonymous)return login(true);
 if(S.appr===null)return`<p>A verificar a conta…</p>`;
 if(!S.appr)return`<div class="card"><h2>Conta à espera de aprovação</h2><p>${S.prof?"O administrador aprova-te na aplicação. Se precisares, envia-lhe este código:":"Falta o perfil. Sai e cria a conta de novo."}</p><p style="word-break:break-all;font-weight:700;user-select:all">${esc(S.me.uid)}</p>${S.err?`<div class="err">${esc(S.err)}</div>`:""}<button class="btn" data-out="1">Sair</button></div>`;
 if(!S.chat.length)driverInit();
 let h=`<div class="drv"><div class="topbar"></div>`;
 if(S.step<5){S.chat.forEach(c=>h+=c.w=="a"?`<div class="a">${esc(c.t)}</div>`:`<div class="u2">${esc(c.t)}</div>`);
  let o=S.opts;if(S.step==0){o=og().map((p,i)=>({k:"o"+i,l:p}));const l=lastRid();if(l)o.unshift({k:"L",l:`Repetir a última: ${l.de} → ${l.para}`})}
  else if(S.step==1)o=dl().map((r,i)=>({k:"d"+i,l:r.para}));
  h+=`<div class="ans">${o.map(x=>`<button class="btn" data-ans="${x.k}">${esc(x.l)}</button>`).join("")}</div>`;
  if(S.step<2&&!act().length)h+=`<div class="card mu">Ainda não há rotas activas. O administrador tem de criar a primeira.</div>`;
  h+=`${S.gm?`<p class="mu">${esc(S.gm)}</p>`:""}<button class="btn" data-out="1">Sair da conta</button>`}
 else{const l=lot(S.cap,S.occ,0);
  h+=`<div class="a">${esc(S.msg)}</div>${S.gm?`<p class="mu">${esc(S.gm)}</p>`:""}${S.err?`<div class="warn">${esc(S.err)}</div>`:""}<div class="card" style="text-align:center"><div class="mu">${esc(S.de)} → ${esc(S.pa)}</div><div class="mu">Lugares livres</div><div class="num ${l.c}">${l.free}</div><div><span class="tag ${l.c}">${l.tx}</span></div><div class="mu" style="margin-top:6px">${S.occ} de ${S.cap} ocupados · ${esc(S.net)}</div></div>
  <div class="sep">Quantos subiram?</div><div class="ops up">${[1,2,3,4].map(n=>`<button class="btn" data-op="u${n}">+${n}</button>`).join("")}</div>
  <div class="sep">Quantos desceram?</div><div class="ops dn">${[1,2,3,4].map(n=>`<button class="btn" data-op="d${n}">−${n}</button>`).join("")}</div>
  <div class="row"><button class="btn" data-op="full" style="flex:1;min-height:60px">Táxi cheio</button><button class="btn" data-op="empty" style="flex:1;min-height:60px">Táxi vazio</button></div>
  <button class="btn" data-op="end" style="width:100%;margin-top:12px">Terminar serviço</button>`}
 return h+"</div>"}

/* ---------- Administração: aprovação de motoristas ---------- */
function admin(){
 if(!OK)return setup();
 if(!S.me||S.me.isAnonymous)return login(false);
 if(!S.adm)return`<div class="card"><h2>Sem permissão</h2><p>Esta conta não é de administrador.</p><button class="btn" data-out="1">Sair</button></div>`;
 const err=S.err?`<div class="err">${esc(S.err)}</div>`:"",pend=S.drv.filter(d=>!S.apprIds.has(d.id)),done=S.drv.filter(d=>S.apprIds.has(d.id));
 const dv=(d,a)=>`<div class="row" style="align-items:center;margin-top:8px"><div style="flex:1"><b>${esc(d.nome)}</b> · ${esc(d.matricula)}<br><span class="mu">${esc(d.telefone)}</span></div><button class="btn ${a?"":"p"}" data-${a?"rv":"ap"}="${esc(d.id)}">${a?"Revogar":"Aprovar"}</button></div>`;
 return`<h2>Motoristas</h2>${err}<div class="card"><b>Por aprovar (${pend.length})</b>${pend.map(d=>dv(d,0)).join("")}</div><div class="card"><b>Aprovados (${done.length})</b>${done.map(d=>dv(d,1)).join("")}</div>
 <h2 style="margin-top:16px">Rotas</h2><div class="card">${ROUTES.map(r=>{const g=S.geo[r.id];return`<div class="row" style="align-items:center;margin-top:8px"><div style="flex:1"><b>${esc(r.de)} → ${esc(r.para)}</b><br><span class="mu">${g?"percurso de "+String(g.km).replace(".",",")+" km":"sem percurso (calcula-se quando um motorista a escolher)"}</span></div>${g?`<button class="btn" data-dg="${r.id}">Apagar percurso</button>`:""}</div>`}).join("")}<p class="mu">Lista fixa na app (a validar com taxistas). Apagar o percurso força um novo cálculo.</p></div>`}
async function adm(k){S.err="";
 try{if(k.startsWith("ap"))await setDoc(doc(db,"approved",k.slice(2)),{ok:true,quando:serverTimestamp()});else if(k.startsWith("rv"))await deleteDoc(doc(db,"approved",k.slice(2)));else if(k.startsWith("dg"))await deleteDoc(doc(db,"routes",k.slice(2)))}
 catch(e){S.err="Erro ("+(e.code||"?")+")."}}

/* ---------- Render e eventos ---------- */
function render(){
 if(document.activeElement&&document.activeElement.matches("input"))return;
 $("swap").innerHTML=S.mode=="start"?"":`<button class="btn" data-m="start" style="min-height:40px">Trocar</button>`;
 $("top").innerHTML=navigator.onLine?"":`<div class="warn">Sem internet. Os dados podem estar desactualizados.</div>`;
 if(S.mode=="p"&&S.dest)$("top").innerHTML+=`<div class="row" style="align-items:center;margin:0 16px 10px"><div style="flex:1"><div class="mu">A ir para</div><b style="font-size:1.4rem">${esc(S.dest)}</b></div><button class="btn" data-dest="">Mudar destino</button></div>`;
 $("app").innerHTML=({start,p:passenger,t:taxista,a:admin})[S.mode]()}
function locate(){if(!navigator.geolocation){S.err="Este navegador não tem localização.";render();return}
 navigator.geolocation.getCurrentPosition(p=>{S.upos=[p.coords.latitude,p.coords.longitude];S.prev={};track();render()},e=>{S.err=e.code==1?"Sem permissão de localização. Permite-a nas definições do navegador.":"Não consegui obter a tua localização.";render()},{enableHighAccuracy:true,timeout:15000})}
document.addEventListener("click",async e=>{const b=e.target.closest("button,[data-t]");if(!b)return;const d=b.dataset;
 if(d.m){if(S.svc&&d.m!="t")await endSvc();S.mode=d.m;S.sel=null;S.err="";if(d.m=="p")openPassenger()}
 if("dest"in d){S.dest=d.dest||null;S.sel=null}if(d.t)S.sel=d.t;if(d.x)S.sel=null;
 if(d.rg)S.range=+d.rg;if(d.loc)locate();
 if(d.reg){S.reg=!S.reg;S.err=""}if(d.auth)await doAuth();
 if(d.out){await endSvc();await signOut(auth);S.chat=[]}
 if(d.ans)await answer(d.ans);
 if(d.op){const o=d.op;if(o[0]=="u")setOcc(S.occ+ +o[1],`+${o[1]} registado.`);else if(o[0]=="d")setOcc(S.occ-+o[1],`−${o[1]} registado.`);else if(o=="full")setOcc(S.cap,"Marcado como cheio.");else if(o=="empty")setOcc(0,"Marcado como vazio.");else if(o=="end")await endSvc()}
 if(d.dg)await adm("dg"+d.dg);if(d.ap)await adm("ap"+d.ap);if(d.rv)await adm("rv"+d.rv);
 render()});
addEventListener("online",render);addEventListener("offline",render);
setInterval(()=>{if(S.mode=="p"&&S.ready)render()},5000);
render();
