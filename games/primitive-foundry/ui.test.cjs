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
      if(!attr)return [];
      const matches=[...this.innerHTML.matchAll(new RegExp('data-'+attr+'="([^"]+)"','g'))];
      const out=matches.map((m,i)=>{
        const e=element(id+"-"+attr+"-"+i);e.dataset={[attr]:m[1]};return e;
      });
      caches.set(key,out);return out;
    }
   };
   if(id==="factory-canvas"){
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
 get("factory-tech").textContent=tech;
 const doc={
  getElementById:get,
  querySelectorAll(s){return s==="[data-category]"?cats:
    s==="[data-panel]"?panels:[];},
  addEventListener(){}
 };
 return {get,doc,cats,panels};
}

test("standalone page embeds all UI, engine and source-backed tech tree without external scripts",()=>{
 assert.match(index,/name="viewport"/);
 assert.match(index,/id="factory-canvas"/);
 assert.match(index,/id="technologies"/);
 assert.match(index,/id="documents"/);
 assert.match(index,/data-category="production"/);
 assert.match(play,/id="factory-tech"/);
 assert.ok(play.includes(engine),"engine bundle must match checked source");
 assert.ok(play.includes(ui),"UI bundle must match checked source");
 assert.equal(JSON.parse(play.match(/<script type="application\/json" id="factory-tech">([\s\S]*?)<\/script>/)[1]).nodes.length,10);
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
 assert.ok(storage.has("primitive-foundry-save-v1"),"actual game should autosave");
 const w=JSON.parse(storage.get("primitive-foundry-save-v1"));
 assert.ok(w.tick>=24&&w.tiles.length===F.SIZE);
 // Select the existing assembler in the provided blueprinted factory.
 const canvas=f.get("factory-canvas");
 const x=760/2+(11.5-11.8)*31,y=520/2+(7.5-8.4)*31;
 canvas.handlers.pointerdown({button:0,pointerId:1,clientX:x,clientY:y,preventDefault(){}});
 canvas.handlers.pointerup({preventDefault(){}});
 assert.match(f.get("inspector").innerHTML,/組立機/);
 f.cats[1].handlers.click();
 assert.match(f.get("tools").innerHTML,/銅の炉/);
 const btn=f.get("tools").querySelectorAll("[data-tool]").find(x=>x.dataset.tool==="ironFurnace");
 assert.ok(btn);btn.handlers.click();
 const fx=760/2+(16.5-11.8)*31,fy=520/2+(8.5-8.4)*31;
 canvas.handlers.pointerdown({button:0,pointerId:1,clientX:fx,clientY:fy,preventDefault(){}});
 canvas.handlers.pointerup({preventDefault(){}});
 const built=JSON.parse(storage.get("primitive-foundry-save-v1"));
 assert.equal(built.tiles[F.idx(16,8)].building.kind,"ironFurnace");
 assert.match(f.get("inspector").innerHTML,/鉄の精錬炉/);
 f.get("play").handlers.click();
 assert.match(f.get("play").textContent,/再開/);
});

test("UI tech buttons reference actual source nodes rather than placeholder theorem names",()=>{
 assert.match(ui,/source-backed tech|証明参照|数学的な出典/);
 assert.match(ui,/F\.techAvailable/);
 assert.match(ui,/F\.unlock/);
 assert.match(ui,/F\.isDiscovered/);
 assert.match(index,/id="view-research"/);
});
