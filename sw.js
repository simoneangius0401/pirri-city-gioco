/* Pirri City: copia locale del gioco per giocare senza internet.
   Ogni file chiesto dal gioco (pagina, modelli, quartieri della mappa grande) viene salvato; se manca la rete si usa la copia.
   Con la rete si prende sempre la versione nuova (cosi' gli aggiornamenti arrivano). */
const C='pirri-city';
self.addEventListener('install',e=>self.skipWaiting());
self.addEventListener('activate',e=>e.waitUntil(self.clients.claim()));
self.addEventListener('fetch',e=>{const r=e.request;if(r.method!=='GET')return;let u;try{u=new URL(r.url)}catch(x){return}if(u.origin!==location.origin)return;
 e.respondWith((async()=>{const c=await caches.open(C);try{const res=await fetch(r);if(res&&res.ok&&res.type!=='opaque')c.put(r,res.clone()).catch(()=>{});return res}
  catch(err){const hit=await c.match(r,{ignoreSearch:true})||await c.match(u.pathname,{ignoreSearch:true});if(hit)return hit;if(r.mode==='navigate'){const pg=await c.match('./',{ignoreSearch:true});if(pg)return pg}return Response.error()}})())});
