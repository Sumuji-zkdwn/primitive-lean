"use strict";
const {test}=require("node:test");
const assert=require("node:assert/strict");
const fs=require("node:fs");
const path=require("node:path");
const vm=require("node:vm");
const root=__dirname;
const load=name=>fs.readFileSync(path.join(root,name),"utf8");
const modelScript=load("atlas.js"),uiScript=load("ui.js"),html=load("index.html"),offline=load("play.html");

function browserMock(phone=true){
 const elements=new Map(),storage=new Map(),tabs=["read","deps","lean"],events={};
 const ctx={};
 for(const name of ["setTransform","fillRect","beginPath","moveTo","lineTo","bezierCurveTo","stroke","arc","fill","fillText","setLineDash","save","restore"])
  ctx[name]=()=>{};
 function node(id){
  const ev={},attrs={},cs=new Set(),cache=new Map();
  let inner="",value="";
  const element={
   id,ev,attrs,dataset:{},style:{},hidden:false,
   get value(){return value;},set value(x){value=x;},
   textContent:"",width:0,height:0,
   classList:{add(x){cs.add(x);},remove(x){cs.delete(x);},contains(x){return cs.has(x);},toggle(x,on){on?cs.add(x):cs.delete(x);}},
   setAttribute(k,v){attrs[k]=v;},
   addEventListener(k,fn){ev[k]=fn;},
   getBoundingClientRect(){return {left:0,top:0,width:phone?412:1080,height:phone?380:620};},
   setPointerCapture(){},blur(){},focus(){},
   get innerHTML(){return inner;},
   set innerHTML(x){inner=String(x);cache.clear();},
   querySelectorAll(selector){
    const m=/^\[data-([a-z-]+)\]$/.exec(selector);
    if(!m)return [];
    const attr=m[1],k=selector+"|"+inner;
    if(cache.has(k))return cache.get(k);
    const values=[...inner.matchAll(new RegExp('data-'+attr+'="([^"]+)"','g'))].map((found,i)=>{
     const e=node(id+"-"+attr+"-"+i);const camel=attr.replace(/-([a-z])/g,(_,c)=>c.toUpperCase());
     e.dataset[camel]=found[1];return e;
    });
    cache.set(k,values);return values;
   },
   querySelector(sel){return this.querySelectorAll(sel)[0]||null;},
   click(){if(ev.click)ev.click();}
  };
  return element;
 }
 const get=id=>{
  if(!elements.has(id))elements.set(id,node(id));
  return elements.get(id);
 };
 get("graph").parentElement=get("stage");
 get("graph").getContext=()=>ctx;
 get("atlas-graph").textContent=load("graph.json");
 get("atlas-proofs").textContent=load("proofs.json");
 get("atlas-narratives").textContent=load("narratives.json");
 const tabElements=tabs.map(tab=>{const x=node("reader-tab-"+tab);x.dataset.readerTab=tab;return x;});
 const body=node("body");
 const document={
  body,
  getElementById:get,
  querySelectorAll(selector){return selector==="[data-reader-tab]"?tabElements:[];},
  addEventListener(name,fn){events[name]=fn;}
 };
 const sandbox={
  document,window:{innerWidth:phone?412:1200},
  globalThis:null,devicePixelRatio:1,URLSearchParams,URL,
  location:{search:"?n=230",href:"https://example.com/play.html?n=230"},
  history:{replaceState(){}},
  localStorage:{getItem:k=>storage.get(k)||null,setItem:(k,v)=>storage.set(k,v)},
  ResizeObserver:class{observe(){}},
  fetch(){throw Error("The standalone page must not access the network")},
  console,Math,JSON
 };
 sandbox.globalThis=sandbox;
 return {document,get,sandbox,storage,tabs:tabElements,events};
}
async function boot(phone=true){
 const b=browserMock(phone);
 vm.runInNewContext(modelScript,b.sandbox,{timeout:5000});
 vm.runInNewContext(uiScript,b.sandbox,{timeout:8000});
 await new Promise(resolve=>setTimeout(resolve,0));
 return b;
}

test("offline atlas contains all source records, narration and scripts without network links",()=>{
 assert.match(html,/name="viewport"/);
 assert.match(html,/id="graph"/);
 assert.match(html,/id="reader"/);
 assert.match(html,/data-reader-tab="lean"/);
 assert.match(offline,/id="atlas-graph"/);
 assert.match(offline,/id="atlas-proofs"/);
 assert.match(offline,/id="atlas-narratives"/);
 assert.ok(offline.includes(modelScript));
 assert.ok(offline.includes(uiScript));
 assert.equal((offline.match(/<script src=/g)||[]).length,0);
 const scripts=[...offline.matchAll(/<script id="atlas-([a-z-]+)" type="application\/json">([\s\S]*?)<\/script>/g)];
 assert.equal(scripts.length,3);
 assert.equal(JSON.parse(scripts.find(x=>x[1]==="graph")[2]).nodes.length,465);
 assert.equal(JSON.parse(scripts.find(x=>x[1]==="proofs")[2]).records.length,465);
});

test("Android can search, inspect real proof arguments, navigate sources and use graph gestures",async()=>{
 const b=await boot(true);
 const {get,tabs}=b;
 assert.equal(get("number").textContent,"#230");
 assert.match(get("theorem-title").textContent,/観測|座標|入力/);
 assert.match(get("reader-content").innerHTML,/2回の観測|2点/);
 get("open-reader").ev.click();
 assert.equal(b.document.body.classList.contains("reader-open"),true);
 tabs[1].ev.click();
 assert.match(get("reader-content").innerHTML,/証明項|直接参照/);
 assert.ok(get("reader-content").querySelectorAll("[data-node]").length>=3);
 tabs[2].ev.click();
 assert.match(get("reader-content").innerHTML,/theorem two_inputs_iff_pair/);
 assert.match(get("reader-content").innerHTML,/GitHubで元の証明/);
 const canvas=get("graph");
 canvas.ev.pointerdown({button:0,pointerId:1,clientX:80,clientY:90,preventDefault(){}});
 canvas.ev.pointerdown({button:0,pointerId:2,clientX:170,clientY:90,preventDefault(){}});
 canvas.ev.pointermove({pointerId:2,clientX:210,clientY:90,preventDefault(){}});
 canvas.ev.pointerup({pointerId:2,clientX:210,clientY:90,preventDefault(){}});
 canvas.ev.pointerup({pointerId:1,clientX:80,clientY:90,preventDefault(){}});
 get("overview").ev.click();
 assert.equal(get("overview").attrs["aria-pressed"],"true");
 get("focus").ev.click();
 assert.equal(get("focus").attrs["aria-pressed"],"true");
 get("search").ev.input({target:{value:"unit_speed_squared"}});
 const hits=get("hits").querySelectorAll("[data-hit]");
 assert.ok(hits.length>0);
 hits[0].ev.click();
 assert.match(get("reader-content").innerHTML,/弧長再構成|速度は常に1/);
 assert.match(get("number").textContent,/#102/);
 get("close-reader").ev.click();
 assert.equal(b.document.body.classList.contains("reader-open"),false);
});

test("manual connections are separately labeled, annotated and persisted without affecting proofs",async()=>{
 const b=await boot(true);
 const {get,tabs,storage}=b;
 tabs[1].ev.click();
 assert.match(get("reader-content").innerHTML,/探索リンク/);
 get("begin-link").ev.click();
 assert.match(get("reader-content").innerHTML,/相手を選択中/);
 get("search").ev.input({target:{value:"unit_speed_squared"}});
 const hits=get("hits").querySelectorAll("[data-hit]");
 assert.ok(hits.length);
 hits[0].ev.click();
 assert.match(get("reader-content").innerHTML,/点線として保存/);
 get("link-note").value="異なる分野を比較したい。証明の一部とは主張しない。";
 get("save-link").ev.click();
 const saved=JSON.parse(storage.get("primitive-atlas-v1"));
 assert.equal(saved.links.length,1);
 assert.equal(saved.links[0].from,229);
 assert.equal(saved.links[0].to,101);
 assert.match(saved.links[0].note,/異なる分野/);
 assert.equal(get("number").textContent,"#230","user link creation should not silently change theorem selection");
 assert.match(get("reader-content").innerHTML,/探索リンク/);
 get("reader-content").querySelectorAll("[data-del]")[0].ev.click();
 assert.equal(JSON.parse(storage.get("primitive-atlas-v1")).links.length,0);
});

test("desktop interface preserves graph canvas and theorem reading panel",async()=>{
 const b=await boot(false);
 assert.equal(b.get("reader").id,"reader");
 assert.equal(b.get("graph").height,620);
 assert.equal(b.get("theorem-title").textContent.length>0,true);
 assert.ok(b.get("reader-content").innerHTML.length>50);
});

test("reader exposes collapsible arguments and complete reference cards",async()=>{
 const b=await boot(true),content=b.get("reader-content");
 assert.match(content.innerHTML,/論証を展開 · [0-9]+段階/);
 assert.match(content.innerHTML,/前提の論証を展開 · 3件/);
 assert.equal(content.querySelectorAll("[data-proof-ancestor]").length,3);
 assert.match(content.innerHTML,/さらに詳しい日本語論証を依頼する/);
 assert.match(content.innerHTML,/id="argument-packet" readonly/);
 assert.match(content.innerHTML,/LinearInputObservation.two_inputs_iff_pair/);
 assert.match(content.innerHTML,/recover_coordinate/);
 b.get("search").ev.input({target:{value:"globalMin_iff_margin"}});
 b.get("hits").querySelectorAll("[data-hit]")[0].ev.click();
 assert.match(content.innerHTML,/大域的最小性の必要十分条件/);
 assert.match(content.innerHTML,/前提の論証を展開 · 4件/);
 assert.equal(content.querySelectorAll("[data-proof-ancestor]").length,4);
});
