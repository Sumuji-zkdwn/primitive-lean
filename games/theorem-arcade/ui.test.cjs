"use strict";
const {test}=require("node:test");
const assert=require("node:assert/strict");
const vm=require("node:vm");
const fs=require("node:fs");
const path=require("node:path");
const E=require("./engine.js");

test("phone document is responsive and loads the three engine modules",()=>{
  const html=fs.readFileSync(path.join(__dirname,"index.html"),"utf8");
  assert.match(html,/name="viewport"/);
  assert.match(html,/src="\.\/engine\.js"/);
  assert.match(html,/src="\.\/ui\.js"/);
  for(const id of ["sand-mode","la-mode","ca-mode","sand-80","sand-81","la-edges","ca-canvas"])
    assert.ok(html.includes('id="'+id+'"'),"missing UI: "+id);
});

test("scripts boot on a mobile-like document, and interaction triggers the mathematical traces",()=>{
  const elems=new Map();
  const make=(id)=>({
    id,innerHTML:"",textContent:"",disabled:false,dataset:{},attrs:{},events:{},
    classList:{toggle(){}},
    addEventListener(name,cb){this.events[name]=cb;},
    setAttribute(name,val){this.attrs[name]=val;},
    getContext(){return {clearRect(){},fillRect(){},fillStyle:null};},
    getBoundingClientRect(){return {left:0,top:0,width:510,height:510};},
    querySelectorAll(){return []}
  });
  const get=(id)=>{
    if(!elems.has(id))elems.set(id,make(id));
    return elems.get(id);
  };
  const tabs=["sand","la","ca"].map(t=>{
    const el=make("tab-"+t);el.dataset.tab=t;return el;
  });
  const document={
    getElementById:get,
    querySelectorAll(sel){return sel==="[data-tab]"?tabs:[];}
  };
  let tick=null;
  const sandbox={TheoremArcade:E,document,setInterval(fn){tick=fn;return 1;},clearInterval(){tick=null;}};
  sandbox.globalThis=sandbox;
  const ui=fs.readFileSync(path.join(__dirname,"ui.js"),"utf8");
  vm.runInNewContext(ui,sandbox,{timeout:4000});
  assert.equal(get("sand-a").textContent,"0");
  assert.equal(get("sand-b").textContent,"0");
  assert.equal(get("sand-observe").textContent,"一致");
  assert.equal(get("la-reach").textContent,"12 / 12");
  assert.equal(get("la-parity").textContent,"奇");
  assert.equal(get("ca-tick").textContent,"0");

  get("sand-80").events.click();
  assert.equal(get("sand-a").textContent,"95");
  assert.equal(get("sand-b").textContent,"95");
  get("sand-81").events.click();
  assert.equal(get("sand-a").textContent,"95");
  assert.equal(get("sand-b").textContent,"158");
  assert.equal(get("sand-observe").textContent,"一致");
  get("sand-undo").events.click();
  assert.equal(get("sand-b").textContent,"95");
  get("sand-reset").events.click();
  assert.equal(get("sand-round").textContent,"0回");

  get("la-reset").events.click();
  assert.equal(get("la-reach").textContent,"12 / 12");
  assert.match(get("la-graph").innerHTML,/data-node="8"/);
  assert.match(get("la-edges").innerHTML,/data-edge="3"/);
  get("ca-step").events.click();
  assert.equal(get("ca-tick").textContent,"1");
  assert.equal(get("ca-count").textContent,"289");
  get("ca-3").events.click();
  assert.equal(get("ca-count").textContent,"0");
  assert.equal(get("ca-3").attrs["aria-pressed"],"true");
  get("ca-play").events.click();
  assert.ok(tick);
  tick();
  assert.equal(get("ca-count").textContent,"9");
  tabs[0].events.click();
  assert.equal(tick,null,"switching chapter stops cellular automaton timer");
  assert.equal(tabs[0].attrs["aria-selected"],"true");
});
