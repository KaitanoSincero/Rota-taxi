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
 chat:[],step:0,de:"",pa:"",rt:null,opts:[],cap:15,occ:0,svc:false,pos:null,posT:0,msg:"",net:"",fit:false,lastPush:0,rid:null,drv:[],apprIds:new Set()};
let unsub=null,subR=null,subA=null,watchId=null,tick=null,wl=null,map=null,layer=null,bgId=null;
// Na app Android (Capacitor) a localização em segundo plano vem do plugin; no navegador usa-se o GPS normal.
const CAP=window.Capacitor,BG=(CAP&&CAP.isNativePlatform&&CAP.isNativePlatform())?CAP.registerPlugin("BackgroundGeolocation"):null;

const ms=t=>t&&t.toMillis?t.toMillis():NOW();
const age=d=>NOW()-ms(d.t),ageO=d=>NOW()-ms(d.to);
function km(a,b,c,d){const R=6371,p=Math.PI/180,x=Math.sin((c-a)*p/2)**2+Math.cos(a*p)*Math.cos(c*p)*Math.sin((d-b)*p/2)**2;return 2*R*Math.asin(Math.sqrt(x))}
function lot(cap,occ,a){const free=cap-occ;let c="g",tx="Lugares livres";if(free<=0){c="r";tx="Cheio"}else if(free<=Math.ceil(cap*.25)){c="y";tx="Poucos lugares"}if(a>STALE_OCC){c="u";tx="Lotação desconhecida"}return{c,tx,free,old:a>STALE_OCC}}
const tag=l=>`<span class="tag ${l.c}">${l.tx}${l.old?"":" · "+l.free+" livres"}</span>`;
const act=()=>S.routes.filter(r=>r.ativa);
function prep(r){const P=Array.isArray(r.paragens)?r.paragens:[];r.paragens=P;if(P.length){const k=M*Math.cos(P[0].lat*Math.PI/180);r._k=k;r._xy=P.map(p=>[p.lng*k,p.lat*M]);r._c=[0];for(let i=1;i<P.length;i++)r._c.push(r._c[i-1]+Math.hypot(r._xy[i][0]-r._xy[i-1][0],r._xy[i][1]-r._xy[i-1][1]))}return r}
// Projecta um ponto no percurso (paragens em ordem): devolve a distância ao longo da rota e o desvio, em metros.
function proj(r,lat,lng){if(!r._xy||r._xy.length<2)return null;const p=[lng*r._k,lat*M];let b=null;
 for(let i=0;i<r._xy.length-1;i++){const A=r._xy[i],B=r._xy[i+1],dx=B[0]-A[0],dy=B[1]-A[1],L2=dx*dx+dy*dy||1;let t=((p[0]-A[0])*dx+(p[1]-A[1])*dy)/L2;t=Math.max(0,Math.min(1,t));
  const off=Math.hypot(p[0]-(A[0]+t*dx),p[1]-(A[1]+t*dy));if(!b||off<b.off)b={off,along:r._c[i]+t*Math.sqrt(L2)}}return b}
function nearStop(r,u){if(!u||!r.paragens.length)return null;let b=null;r.paragens.forEach((s,i)=>{const m=km(u[0],u[1],s.lat,s.lng)*1000;if(!b||m<b.m)b={i,m,n:s.n}});return b&&b.m<=800?b:null}
function eta(d){const r=S.routes.find(x=>x.id==d.rid);if(!r||!r._xy||r._xy.length<2)return{t:"rota sem paragens registadas"};
 if(!S.upos)return{t:"activa a tua localização para ver o tempo"};const ns=nearStop(r,S.upos);if(!ns)return{t:"esta rota não passa a menos de 800 m de ti",o:1};
 const p=proj(r,d.lat,d.lng);if(!p||p.off>300)return{t:"fora do percurso",o:1};const gap=r._c[ns.i]-p.along;
 if(gap<-40)return{t:"já passou a paragem "+ns.n,o:1};return{t:`~${Math.max(1,Math.round(gap/SPEED))} min até ${ns.n} (${Math.round(Math.max(0,gap))} m)`,g:Math.max(0,gap),ok:1}}

/* ---------- Ligação ---------- */
function subLive(){if(unsub||!OK)return;unsub=onSnapshot(collection(db,"live"),snap=>{S.live=snap.docs.map(d=>({id:d.id,...d.data()}));S.ready=true;S.err="";render()},e=>{S.err="Erro a ler os táxis ("+e.code+").";render()})}
function subRoutes(){if(subR||!OK)return;subR=onSnapshot(collection(db,"routes"),snap=>{S.routes=snap.docs.map(d=>prep({id:d.id,...d.data()}));render()},e=>{S.err="Erro a ler as rotas ("+e.code+").";render()})}
function subAdmin(){if(subA||!S.adm)return;subA=[onSnapshot(collection(db,"drivers"),x=>{S.drv=x.docs.map(d=>({id:d.id,...d.data()}));render()},()=>{}),onSnapshot(collection(db,"approved"),x=>{S.apprIds=new Set(x.docs.map(d=>d.id));render()},()=>{})]}
async function openPassenger(){
 if(!OK)return;
 try{if(!auth.currentUser)await signInAnonymously(auth)}catch(e){S.err="Não foi possível entrar. Verifica a internet e se o login anónimo está activo no Firebase.";render();return}
 subLive();subRoutes();
 if(navigator.geolocation&&!S.upos)navigator.geolocation.getCurrentPosition(p=>{S.upos=[p.coords.latitude,p.coords.longitude];render()},()=>{},{maximumAge:60000,timeout:8000});
}
if(OK)onAuthStateChanged(auth,async u=>{
 [unsub,subR].forEach(f=>f&&f());unsub=subR=null;(subA||[]).forEach(f=>f());subA=null;
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

function passenger(){
 if(!OK)return setup();
 const fresh=S.live.filter(d=>age(d)<=STALE_POS);
 if(!S.dest){
  const cnt={};fresh.forEach(d=>cnt[d.para]=(cnt[d.para]||0)+1);
  const all=[...new Set(act().map(r=>r.para))].sort((a,b)=>(cnt[b]||0)-(cnt[a]||0)||a.localeCompare(b,"pt"));
  return(S.err?`<p class="err">${esc(S.err)}</p>`:"")+`<h2 style="font-size:1.3rem;margin-top:8px">Para onde vais?</h2>`+
   (all.length?`<p class="mu">Escolhe o destino final.</p>`+all.map(p=>`<button class="item" data-dest="${esc(p)}" style="font-size:1.1rem"><b>${esc(p)}</b><span class="${cnt[p]?"g":"mu"}">${cnt[p]?cnt[p]+" táxi(s)":"nenhum agora"}</span></button>`).join(""):`<div class="card mu">${S.ready||S.routes.length?"Ainda não há rotas activas.":"A ligar…"}</div>`)}
 const all=S.live.filter(d=>d.para==S.dest),vis=all.filter(d=>age(d)<=STALE_POS),old=all.length-vis.length;
 const rows=vis.map(d=>({d,e:eta(d),l:lot(d.cap,d.occ,ageO(d))})).sort((a,b)=>(!!b.e.ok-!!a.e.ok)||((a.e.g??9e9)-(b.e.g??9e9)));
 let h=(S.err?`<p class="err">${esc(S.err)}</p>`:"")+`<h2 style="margin-top:4px">Táxis para ${esc(S.dest)}</h2>`;
 if(!rows.length)h+=`<div class="card mu">Nenhum táxi para ${esc(S.dest)} com posição actual neste momento.</div>`;
 rows.forEach(({d,e,l})=>h+=`<button class="item" data-t="${esc(d.id)}" style="${e.o?"opacity:.6":""}"><span><b>${esc(d.veic||"Táxi")}</b><br><span class="mu">vem de ${esc(d.de)} · ${esc(e.t)}</span></span><span style="text-align:right">${tag(l)}</span></button>`);
 if(old)h+=`<p class="mu">${old} táxi(s) escondido(s): sem sinal há mais de 90 s.</p>`;
 h+=`<p class="mu">Tempo aproximado calculado a 15 km/h ao longo das paragens registadas. Não considera trânsito; confirma sempre a localização.</p>`;
 const t=S.sel&&all.find(x=>x.id==S.sel);
 if(t){const l=lot(t.cap,t.occ,ageO(t));h+=`<div class="card" style="border-color:var(--pri)"><h2>${esc(t.veic||"Táxi")}</h2><div>Rota: ${esc(t.de)} → ${esc(t.para)}</div><div>${tag(l)}</div><div class="mu">Posição: há ${Math.round(age(t)/1000)} s · lotação: há ${Math.round(ageO(t)/1000)} s · posição aproximada (precisão variável conforme o GPS)</div><button class="btn" data-x="1" style="margin-top:8px">Fechar</button></div>`}
 return h}
function drawMap(on,list){
 const el=$("mapbox");if(!on||typeof L=="undefined"){el.hidden=true;return}
 el.hidden=false;
 if(!map){map=L.map(el).setView([-8.839,13.289],12);L.tileLayer("https://tile.openstreetmap.org/{z}/{x}/{y}.png",{maxZoom:19,attribution:"© OpenStreetMap"}).addTo(map);layer=L.layerGroup().addTo(map)}
 map.invalidateSize();layer.clearLayers();const pts=[];
 act().filter(r=>r.para==S.dest).forEach(r=>{if(r.paragens.length>1)L.polyline(r.paragens.map(p=>[p.lat,p.lng]),{color:"#1550b8",weight:4,opacity:.4}).addTo(layer);
  r.paragens.forEach(p=>{pts.push([p.lat,p.lng]);L.circleMarker([p.lat,p.lng],{radius:5,color:"#1550b8",weight:2,fillColor:"#fff",fillOpacity:1}).bindTooltip(p.n).addTo(layer)})});
 list.forEach(d=>{const l=lot(d.cap,d.occ,ageO(d));pts.push([d.lat,d.lng]);L.circleMarker([d.lat,d.lng],{radius:11,color:"#fff",weight:3,fillColor:COL[l.c],fillOpacity:1}).addTo(layer).on("click",()=>{S.sel=d.id;render()})});
 if(S.upos){L.circleMarker(S.upos,{radius:7,color:"#fff",weight:2,fillColor:"#c0302b",fillOpacity:1}).addTo(layer);pts.push(S.upos)}
 if(!S.fit&&pts.length>1){map.fitBounds(pts,{padding:[30,30],maxZoom:15});S.fit=true}}

/* ---------- Motorista ---------- */
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
 else if(k=="y"){me("Sim, é esta");try{localStorage.setItem("rt_last2",S.rt)}catch(e){}say("Quantos lugares tem o teu táxi?");S.step=3;S.opts=[12,14,15,18].map(n=>({k:"c"+n,l:n+" lugares"}))}
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
  h+=`<button class="btn" data-out="1">Sair da conta</button>`}
 else{const l=lot(S.cap,S.occ,0);
  h+=`<div class="a">${esc(S.msg)}</div>${S.err?`<div class="warn">${esc(S.err)}</div>`:""}<div class="card" style="text-align:center"><div class="mu">${esc(S.de)} → ${esc(S.pa)}</div><div class="mu">Lugares livres</div><div class="num ${l.c}">${l.free}</div><div><span class="tag ${l.c}">${l.tx}</span></div><div class="mu" style="margin-top:6px">${S.occ} de ${S.cap} ocupados · ${esc(S.net)}</div></div>
  <div class="sep">Quantos subiram?</div><div class="ops up">${[1,2,3,4].map(n=>`<button class="btn" data-op="u${n}">+${n}</button>`).join("")}</div>
  <div class="sep">Quantos desceram?</div><div class="ops dn">${[1,2,3,4].map(n=>`<button class="btn" data-op="d${n}">−${n}</button>`).join("")}</div>
  <div class="row"><button class="btn" data-op="full" style="flex:1;min-height:60px">Táxi cheio</button><button class="btn" data-op="empty" style="flex:1;min-height:60px">Táxi vazio</button></div>
  <button class="btn" data-op="end" style="width:100%;margin-top:12px">Terminar serviço</button>`}
 return h+"</div>"}

/* ---------- Administração: rotas, paragens e aprovação de motoristas ---------- */
const okName=v=>/^[\p{L}\p{N} .'()-]{1,30}$/u.test(v);
const saveStops=(r,P)=>updateDoc(doc(db,"routes",r.id),{paragens:P});
function admin(){
 if(!OK)return setup();
 if(!S.me||S.me.isAnonymous)return login(false);
 if(!S.adm)return`<div class="card"><h2>Sem permissão</h2><p>Esta conta não é de administrador.</p><button class="btn" data-out="1">Sair</button></div>`;
 const err=S.err?`<div class="err">${esc(S.err)}</div>`:"",r=S.routes.find(x=>x.id==S.rid);
 if(r){const P=r.paragens;
  return`<button class="btn" data-back="1">‹ Voltar</button><h2 style="margin-top:10px">${esc(r.de)} → ${esc(r.para)}</h2>${err}
  <div class="row" style="margin-bottom:10px"><button class="btn ${r.ativa?"p":""}" data-tog="1" style="flex:1">${r.ativa?"Rota activa (desactivar)":"Rota inactiva (activar)"}</button></div>
  <div class="card"><b>Paragens, por ordem do percurso (${esc(r.de)} → ${esc(r.para)})</b>${P.length?"":`<p class="mu">Ainda sem paragens.</p>`}
  ${P.map((p,i)=>`<div class="row" style="align-items:center;margin-top:8px"><div style="flex:1"><b>${i+1}. ${esc(p.n)}</b><br><span class="mu">${p.lat}, ${p.lng}</span></div><button class="btn" data-mv="${i}:-1" aria-label="Subir">▲</button><button class="btn" data-mv="${i}:1" aria-label="Descer">▼</button><button class="btn" data-mv="${i}:0" aria-label="Apagar">✕</button></div>`).join("")}</div>
  <div class="card"><b>Adicionar paragem</b><p class="mu">Vai à paragem e escreve o nome. A posição vem do GPS deste telemóvel. Adiciona por ordem de percurso.</p>
  <label for="sn">Nome da paragem</label><input id="sn" class="f" maxlength="30"><button class="btn p" data-addstop="1" style="width:100%;min-height:52px">Adicionar na minha posição</button></div>`}
 const pend=S.drv.filter(d=>!S.apprIds.has(d.id)),done=S.drv.filter(d=>S.apprIds.has(d.id));
 const dv=(d,a)=>`<div class="row" style="align-items:center;margin-top:8px"><div style="flex:1"><b>${esc(d.nome)}</b> · ${esc(d.matricula)}<br><span class="mu">${esc(d.telefone)}</span></div><button class="btn ${a?"":"p"}" data-${a?"rv":"ap"}="${esc(d.id)}">${a?"Revogar":"Aprovar"}</button></div>`;
 return`<h2>Rotas</h2>${err}${S.routes.map(x=>`<button class="item" data-rid="${esc(x.id)}"><span><b>${esc(x.de)} → ${esc(x.para)}</b><br><span class="mu">${x.paragens.length} paragem(ns)</span></span><span class="${x.ativa?"g":"u"}">${x.ativa?"activa":"inactiva"}</span></button>`).join("")||`<div class="card mu">Ainda não há rotas.</div>`}
 <div class="card"><b>Nova rota</b><label for="rde">Origem</label><input id="rde" class="f" maxlength="30"><label for="rpa">Destino</label><input id="rpa" class="f" maxlength="30"><button class="btn p" data-newr="1" style="width:100%;min-height:52px">Criar rota</button></div>
 <h2 style="margin-top:16px">Motoristas</h2><div class="card"><b>Por aprovar (${pend.length})</b>${pend.map(d=>dv(d,0)).join("")}</div><div class="card"><b>Aprovados (${done.length})</b>${done.map(d=>dv(d,1)).join("")}</div>`}
async function adm(k,v){S.err="";const r=S.routes.find(x=>x.id==S.rid);
 try{
  if(k=="newr"){const de=$("rde").value.trim(),pa=$("rpa").value.trim();if(!okName(de)||!okName(pa))throw{m:"Origem e destino: 1 a 30 letras ou números."};
   const ref=doc(collection(db,"routes"));await setDoc(ref,{de,para:pa,ativa:false,paragens:[]});S.rid=ref.id}
  else if(k=="tog"){if(!r)throw{m:"Selecciona uma rota."};if(!r.ativa&&r.paragens.length<2)throw{m:"Adiciona pelo menos 2 paragens antes de activar a rota."};await updateDoc(doc(db,"routes",r.id),{ativa:!r.ativa})}
  else if(k=="add"){const n=$("sn").value.trim();if(!okName(n))throw{m:"Nome da paragem: 1 a 30 letras ou números."};if(r.paragens.length>=60)throw{m:"Máximo de 60 paragens."};
   const p=await getPos();if(!p.coords)throw{m:"Sem GPS. Activa a localização e tenta ao ar livre."};
   await saveStops(r,[...r.paragens,{n,lat:r5(p.coords.latitude),lng:r5(p.coords.longitude)}])}
  else if(k.startsWith("mv")){const[i,dlt]=k.slice(2).split(":").map(Number),P=[...r.paragens];if(dlt==0)P.splice(i,1);else{const j=i+dlt;if(j<0||j>=P.length)return;[P[i],P[j]]=[P[j],P[i]]}await saveStops(r,P)}
  else if(k.startsWith("ap"))await setDoc(doc(db,"approved",k.slice(2)),{ok:true,quando:serverTimestamp()});
  else if(k.startsWith("rv"))await deleteDoc(doc(db,"approved",k.slice(2)));
 }catch(e){S.err=e.m||"Erro ("+(e.code||"?")+").";}}

/* ---------- Render e eventos ---------- */
function render(){
 if(document.activeElement&&document.activeElement.matches("input"))return;
 $("swap").innerHTML=S.mode=="start"?"":`<button class="btn" data-m="start" style="min-height:40px">Trocar</button>`;
 $("top").innerHTML=navigator.onLine?"":`<div class="warn">Sem internet. Os dados podem estar desactualizados.</div>`;
 if(S.mode=="p"&&S.dest)drawMap(true,S.live.filter(d=>d.para==S.dest&&age(d)<=STALE_POS));else drawMap(false);
 if(S.mode=="p"&&S.dest)$("top").innerHTML+=`<div class="row" style="align-items:center;margin:0 16px 10px"><div style="flex:1"><div class="mu">A ir para</div><b style="font-size:1.4rem">${esc(S.dest)}</b></div><button class="btn" data-dest="">Mudar destino</button></div>`;
 $("app").innerHTML=({start,p:passenger,t:taxista,a:admin})[S.mode]()}
document.addEventListener("click",async e=>{const b=e.target.closest("button");if(!b)return;const d=b.dataset;
 if(d.m){if(S.svc&&d.m!="t")await endSvc();S.mode=d.m;S.sel=null;S.err="";if(d.m=="p")openPassenger()}
 if("dest"in d){S.dest=d.dest||null;S.sel=null;S.fit=false}if(d.t)S.sel=d.t;if(d.x)S.sel=null;
 if(d.reg){S.reg=!S.reg;S.err=""}if(d.auth)await doAuth();
 if(d.out){await endSvc();await signOut(auth);S.chat=[];S.rid=null}
 if(d.ans)await answer(d.ans);
 if(d.op){const o=d.op;if(o[0]=="u")setOcc(S.occ+ +o[1],`+${o[1]} registado.`);else if(o[0]=="d")setOcc(S.occ-+o[1],`−${o[1]} registado.`);else if(o=="full")setOcc(S.cap,"Marcado como cheio.");else if(o=="empty")setOcc(0,"Marcado como vazio.");else if(o=="end")await endSvc()}
 if(d.rid){S.rid=d.rid;S.err=""}if(d.back)S.rid=null;
 if(d.newr)await adm("newr");if(d.tog)await adm("tog");if(d.addstop)await adm("add");
 if(d.mv)await adm("mv"+d.mv);if(d.ap)await adm("ap"+d.ap);if(d.rv)await adm("rv"+d.rv);
 render()});
addEventListener("online",render);addEventListener("offline",render);
setInterval(()=>{if(S.mode=="p"&&S.ready)render()},5000);
render();
