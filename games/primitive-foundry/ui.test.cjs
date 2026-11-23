"use strict";
const test=require("node:test");
const assert=require("node:assert/strict");
const fs=require("node:fs");
const path=require("node:path");
const vm=require("node:vm");
const F=require("./engine.js");
const index=fs.readFileSync(path.join(__dirname,"index.html"),"utf8");
const play=fs.readFileSync(path.join(__dirname,"play.html"),"utf8");
const engine=fs.readFileSync(path.join(__dirname,"engine.js"),"utf8");
const ui=fs.readFileSync(path.join(__dirname,"ui.js"),"utf8");
const tech=fs.readFileSync(path.join(__dirname,"tech.json"),"utf8");
const upgrades=fs.readFileSync(path.join(__dirname,"upgrades.json"),"utf8");

const contextMethods=["setTransform","fillRect","strokeRect","beginPath","arc","fill","stroke","moveTo","lineTo",
 "closePath","save","restore","translate","rotate","rect","clip","fillText","clearRect","setLineDash"];

function fakeDOM(){
 const all=new Map();
 function element(id){
   const handlers={},attrs={},classes=new Set(),caches=new Map();
   const el={id,handlers,attrs,textContent:"",innerHTML:"",style:{},disabled:false,
    classList:{toggle(k,b){if(b)classes.add(k);else classes.delete(k);},add(k){classes.add(k);},
      remove(k){classes.delete(k);},contains(k){return classes.has(k);}},
    addEventListener(name,fn){handlers[name]=fn;},
    setAttribute(k,v){attrs[k]=v;},
    getBoundingClientRect(){return {left:0,top:0,width:760,height:520};},
    setPointerCapture(){},
    querySelectorAll(selector){
      const key=selector+"|"+this.innerHTML;
      if(caches.has(key))return caches.get(key);
      let attr=null;
      if(selector==="[data-tool]")attr="tool";
      if(selector==="[data-unlock]")attr="unlock";
      if(selector==="[data-proof-jump]")attr="proof-jump";
      if(selector==="[data-proof-nav]")attr="proof-nav";
      if(selector==="[data-proof-result]")attr="proof-result";
      if(!attr)return [];
      const matches=[...this.innerHTML.matchAll(new RegExp('data-'+attr+'="([^"]+)"','g'))];
      const out=matches.map((m,i)=>{
        const e=element(id+"-"+attr+"-"+i);e.dataset={[attr]:m[1]};return e;
      });
      caches.set(key,out);return out;
    }
   };
   if(id==="factory-canvas"||id==="proof-graph"){
     el.getContext=()=>{
       const ctx={};
       for(const k of contextMethods)ctx[k]=()=>{};
       return ctx;
     };
   }
   return el;
 }
 function get(id){
  if(!all.has(id))all.set(id,element(id));
  return all.get(id);
 }
 const cats=["logistics","production","utility"].map(x=>{
  const e=element("category-"+x);e.dataset={category:x};return e;
 });
 const panels=["inspect","research","documents"].map(x=>{
  const e=element("panel-"+x);e.dataset={panel:x};return e;
 });
 const mobile=["factory","build","inspect","research","documents"].map(x=>{
  const e=element("mobile-"+x);e.dataset={mobileScreen:x};return e;
 });
 get("factory-tech").textContent=tech;
 get("factory-upgrades-json").textContent=upgrades;
 const doc={
  body:get("body"),
  getElementById:get,
  querySelectorAll(s){return s==="[data-category]"?cats:
    s==="[data-panel]"?panels:s==="[data-mobile-screen]"?mobile:[];},
  addEventListener(){}
 };
 return {get,doc,cats,panels,mobile};
}

test("standalone page embeds all UI, engine and source-backed tech tree without external scripts",()=>{
 assert.match(index,/name="viewport"/);
 assert.match(index,/id="factory-canvas"/);
 assert.match(index,/id="technologies"/);
 assert.match(index,/id="documents"/);
 assert.match(index,/data-category="production"/);
 assert.match(play,/id="factory-tech"/);
 assert.match(play,/id="factory-upgrades-json"/);
 assert.match(index,/id="proof-graph"/);
 assert.match(index,/id="proof-search"/);
 assert.match(index,/class="mobile-nav"/);
 assert.match(index,/data-mobile-screen="research"/);
 assert.match(index,/orientation:landscape/);
 assert.match(index,/env\(safe-area-inset-bottom\)/);
 assert.match(index,/interactive-widget=resizes-content/);
 assert.ok(play.includes(engine),"engine bundle must match checked source");
 assert.ok(play.includes(ui),"UI bundle must match checked source");
 assert.equal(JSON.parse(play.match(/<script type="application\/json" id="factory-tech">([\s\S]*?)<\/script>/)[1]).nodes.length,465);
 assert.equal(JSON.parse(play.match(/<script type="application\/json" id="factory-upgrades-json">([\s\S]*?)<\/script>/)[1]).nodes.length,10);
 assert.ok(!play.includes('<script src='),"offline build must not depend on external scripts");
});

test("actual phone UI boots, runs simulation, selects buildings and paints construction",async()=>{
 const f=fakeDOM(),storage=new Map(),timers=[];
 const sandbox={
  PrimitiveFoundry:F,window:{innerWidth:1180,addEventListener(){}},
  document:f.doc,globalThis:null,devicePixelRatio:1,
  localStorage:{getItem:k=>storage.get(k)||null,setItem:(k,v)=>storage.set(k,v)},
  setInterval(fn,ms){timers.push(fn);return timers.length;},
  ResizeObserver:class {observe(){}},
  confirm(){return true;},Date,Math,console,
 };
 sandbox.globalThis=sandbox;
 vm.runInNewContext(ui,sandbox,{timeout:4000});
 await new Promise(resolve=>setTimeout(resolve,0));
 assert.equal(timers.length,1);
 assert.ok(f.get("tools").innerHTML.includes("ベルト"));
 assert.ok(f.get("science-total").textContent.includes(" / 30"));
 assert.ok(f.get("viewport").handlers.wheel);
 for(let i=0;i<40;i++)timers[0]();
 assert.ok(storage.has("primitive-foundry-save-v2"),"actual game should autosave");
 const w=JSON.parse(storage.get("primitive-foundry-save-v2"));
 assert.ok(w.tick>=24&&w.tiles.length===F.SIZE);
 // Select the existing assembler in the provided blueprinted factory.
 const canvas=f.get("factory-canvas");
 const x=760/2+(11.5-11.8)*31,y=520/2+(7.5-8.4)*31;
 canvas.handlers.pointerdown({button:0,pointerId:1,clientX:x,clientY:y,preventDefault(){}});
 canvas.handlers.pointerup({preventDefault(){}});
 assert.match(f.get("inspector").innerHTML,/組立機/);
 assert.ok(F.pendingRepairs(w).length===2);
 // Tap the highlighted missing transport cells to repair both links.
 for(const [cx,cy]of [[11,6],[10,8]]){
   const px=760/2+(cx+.5-11.8)*31,py=520/2+(cy+.5-8.4)*31;
   canvas.handlers.pointerdown({button:0,pointerId:1,clientX:px,clientY:py,preventDefault(){}});
   canvas.handlers.pointerup({preventDefault(){}});
 }
 const repaired=JSON.parse(storage.get("primitive-foundry-save-v2"));
 assert.equal(F.pendingRepairs(repaired).length,0);
 f.cats[1].handlers.click();
 assert.match(f.get("tools").innerHTML,/銅の炉/);
 const btn=f.get("tools").querySelectorAll("[data-tool]").find(x=>x.dataset.tool==="ironFurnace");
 assert.ok(btn);btn.handlers.click();
 const fx=760/2+(16.5-11.8)*31,fy=520/2+(8.5-8.4)*31;
 canvas.handlers.pointerdown({button:0,pointerId:1,clientX:fx,clientY:fy,preventDefault(){}});
 canvas.handlers.pointerup({preventDefault(){}});
 const built=JSON.parse(storage.get("primitive-foundry-save-v2"));
 assert.equal(built.tiles[F.idx(16,8)].building.kind,"ironFurnace");
 assert.match(f.get("inspector").innerHTML,/鉄の精錬炉/);
 // The research interface must expose the whole proof DAG (not 10 file nodes).
 f.panels[1].handlers.click();
 assert.match(f.get("proof-metrics").textContent,/465 解明/);
 assert.match(f.get("proof-metrics").textContent,/629直接証明辺/);
 const choices=f.get("proof-results").querySelectorAll("[data-proof-result]");
 assert.ok(choices.length>0&&choices.length<=36);
 choices[0].handlers.click();
 assert.match(f.get("proof-details").innerHTML,/直接の証明前提/);
 assert.match(f.get("proof-details").innerHTML,/前提|研究|解明/);
 assert.ok(f.get("proof-graph").handlers.pointerdown);
 assert.ok(f.get("technologies").innerHTML.includes("証明の前提"));
 f.get("play").handlers.click();
 assert.match(f.get("play").textContent,/再開/);
});

test("UI tech buttons reference actual source nodes rather than placeholder theorem names",()=>{
 assert.match(ui,/証明|直接参照|proof/);
 assert.match(ui,/F\.techAvailable/);
 assert.match(ui,/F\.unlock/);
 assert.match(ui,/F\.isDiscovered/);
 assert.match(index,/id="view-research"/);
 assert.match(ui,/F\.researchProof/);
 assert.match(ui,/tech\.nodes/);
 assert.match(ui,/upgrades\.nodes/);
});


test("Android portrait bottom tabs expose all five screens and graph supports two-finger zoom",async()=>{
 const f=fakeDOM(),storage=new Map(),ticks=[];
 const sandbox={
  PrimitiveFoundry:F,
  window:{innerWidth:412,scrollTo(){},addEventListener(){}},
  document:f.doc,globalThis:null,devicePixelRatio:2,
  localStorage:{getItem:k=>storage.get(k)||null,setItem:(k,v)=>storage.set(k,v)},
  setInterval(fn){ticks.push(fn);return ticks.length;},
  ResizeObserver:class {observe(){}},
  requestAnimationFrame(fn){fn();},
  confirm(){return true;},Date,Math,console
 };
 sandbox.globalThis=sandbox;
 vm.runInNewContext(ui,sandbox,{timeout:6000});
 await new Promise(resolve=>setTimeout(resolve,0));
 assert.ok(f.doc.body.classList.contains("mobile-screen-factory"));
 const tab=name=>f.mobile.find(el=>el.dataset.mobileScreen===name);
 assert.equal(tab("factory").attrs["aria-current"],"page");
 tab("build").handlers.click();
 assert.ok(f.doc.body.classList.contains("mobile-screen-build"));
 assert.equal(tab("build").attrs["aria-current"],"page");
 assert.match(f.get("tools").innerHTML,/ベルト/);
 const map=f.get("factory-canvas");
 map.handlers.pointerdown({button:0,pointerId:1,clientX:250,clientY:220,preventDefault(){}});
 map.handlers.pointerdown({button:0,pointerId:2,clientX:340,clientY:220,preventDefault(){}});
 map.handlers.pointermove({pointerId:2,clientX:400,clientY:220,preventDefault(){}});
 map.handlers.pointerup({pointerId:2,preventDefault(){}});
 map.handlers.pointerup({pointerId:1,preventDefault(){}});
 tab("research").handlers.click();
 assert.ok(f.doc.body.classList.contains("mobile-screen-research"));
 assert.match(f.get("proof-metrics").textContent,/465 解明/);
 assert.match(f.get("proof-results").innerHTML,/data-proof-result/);
 const proof=f.get("proof-graph");
 proof.handlers.pointerdown({pointerId:11,clientX:200,clientY:90,preventDefault(){}});
 proof.handlers.pointerdown({pointerId:12,clientX:290,clientY:90,preventDefault(){}});
 proof.handlers.pointermove({pointerId:12,clientX:340,clientY:90,preventDefault(){}});
 proof.handlers.pointerup({pointerId:12,clientX:340,clientY:90,preventDefault(){}});
 proof.handlers.pointerup({pointerId:11,clientX:200,clientY:90,preventDefault(){}});
 f.get("proof-search").handlers.input({target:{value:"曲率"}});
 assert.match(f.get("proof-result-count").textContent,/465/);
 tab("documents").handlers.click();
 assert.ok(f.doc.body.classList.contains("mobile-screen-documents"));
 assert.match(f.get("documents").innerHTML,/文書|設計書/);
 tab("inspect").handlers.click();
 assert.ok(f.doc.body.classList.contains("mobile-screen-inspect"));
 assert.match(f.get("inspector").textContent,/マップ|工場/);
 tab("factory").handlers.click();
 assert.ok(f.doc.body.classList.contains("mobile-screen-factory"));
 assert.equal(tab("research").attrs["aria-current"],"false");
 assert.equal(ticks.length,1);
});

test("Android landscape direct build and research URLs remain separate from desktop layout",async()=>{
 for(const view of ["build","research"]){
  const f=fakeDOM(),timers=[];
  const sandbox={
   PrimitiveFoundry:F,
   location:{search:"?view="+view},URLSearchParams,
   window:{innerWidth:914,scrollTo(){},addEventListener(){}},
   document:f.doc,globalThis:null,devicePixelRatio:2,
   localStorage:{getItem(){return null;},setItem(){}},
   setInterval(fn){timers.push(fn);return timers.length;},
   ResizeObserver:class {observe(){}},confirm(){return true;},Date,Math,console
  };
  sandbox.globalThis=sandbox;
  vm.runInNewContext(ui,sandbox,{timeout:6000});
  await new Promise(resolve=>setTimeout(resolve,0));
  assert.equal(f.mobile.filter(el=>el.attrs["aria-current"]==="page").length,1);
  assert.ok(f.doc.body.classList.contains("mobile-screen-"+view));
  if(view==="research"){
   assert.match(f.get("proof-metrics").textContent,/629直接証明辺/);
   assert.ok(f.doc.body.classList.contains("research-direct"));
  }
  assert.equal(timers.length,1);
 }
});
