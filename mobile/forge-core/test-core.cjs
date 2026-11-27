const fs=require('fs'),vm=require('vm'),assert=require('assert'),crypto=require('crypto');
const h=fs.readFileSync(__dirname+'/app/src/main/assets/index.html','utf8');
assert.equal(crypto.createHash('sha256').update(h).digest('hex'),'db0e39fc49760640d40c1ad9cb73bd960ea68c3b6d2f9b09389303a9bb2d9006');
const code=h.match(/<script>\s*([\s\S]*?)<\/script>/)[1].split("let model,result")[0];
const snapshot=JSON.parse(h.match(/<script id="snapshot" type="application\/json">([\s\S]*?)<\/script>/)[1]);
vm.runInThisContext(code);
assert.equal(verify(snapshot).count,1); assert.equal(Object.keys(snapshot.actions).length,18);
snapshot.observations.parity=ids(snapshot.n).map(x=>x%2); assert.equal(verify(snapshot).count,256);
snapshot.n++; for(const k of ['observations','actions'])for(const t of Object.values(snapshot[k]))t.push(t[0]);
assert.equal(verify(snapshot).count,256);
snapshot.observations.marker=ids(257).map(x=>Number(x===256)); assert.equal(verify(snapshot).count,257);
let count=0;
for(let o=0;o<8;o++){const obs=[o&1,(o>>1)&1,(o>>2)&1];for(let j=0;j<27;j++){const a=[j%3,Math.floor(j/3)%3,Math.floor(j/9)];const r=verify({n:3,observations:{o:obs},actions:{a}});for(let x=0;x<3;x++)for(let y=x+1;y<3;y++){let u=x,v=y,same=true;for(let i=0;i<3;i++){if(obs[u]!==obs[v])same=false;u=a[u];v=a[v]}assert.equal(r.p[x]===r.p[y],same)}count++}}
assert.equal(count,216); console.log('PASS: actual snapshot and 216 exact models');
