"use strict";
const {test} = require("node:test");
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const vm = require("node:vm");
const html = fs.readFileSync(path.join(__dirname,"index.html"),"utf8");
const engine = html.match(/<script id="hex-engine">([\s\S]*?)<\/script>/);
assert.ok(engine, "independent mobile engine must be embedded in the standalone HTML");
const context = {globalThis:null};
context.globalThis=context;
vm.runInNewContext(engine[1],context,{timeout:3000});
const E=context.HexCircuitEngine;
const asPlain = (x) => JSON.parse(JSON.stringify(x));

test("the HTML can be opened as a standalone mobile document",()=>{
  assert.match(html,/name="viewport"/);
  assert.match(html,/id="board"/);
  assert.match(html,/id="directions"/);
  assert.match(html,/id="hex-ui"/);
  assert.match(html,/id="demo"/);
  assert.match(html,/id="reset"/);
  assert.match(html,/id="auto"/);
  assert.match(html,/games\/hex\/HexGame\.lean/);
});

test("axial hexagon and target ring match Lean",()=>{
  assert.equal(E.CELLS.length,19);
  assert.equal(E.GOALS.length,6);
  assert.deepEqual(asPlain(E.DIRECTIONS),[[1,0],[1,-1],[0,-1],[-1,0],[-1,1],[0,1]]);
  for(const p of E.GOALS) assert.equal(E.inside(p),true);
  assert.deepEqual(asPlain(E.CELLS[0]),[0,-2]);
  assert.equal(E.inside([3,0]),false);
  assert.equal(E.inside([2,1]),false);
});

test("the Lean seven-step solution visits all goals then returns to origin",()=>{
  const path = [[0,0],[1,0],[1,-1],[0,-1],[-1,0],[-1,1],[0,1],[0,0]];
  let s=E.solution();
  assert.equal(s.won,false);
  assert.equal(s.seen.length,0);
  for(let i=1;i<=7;i++){
    s=E.step(s);
    assert.deepEqual(asPlain(s.position),path[i]);
    assert.equal(s.moves,i);
    if(i<7) assert.equal(s.won,false);
    assert.equal(s.lost,false);
  }
  assert.equal(s.won,true);
  assert.equal(s.seen.length,6);
  assert.equal(E.step(s),s,"terminal state must not advance");
});

test("initial eastward route crashes on third tick as Lean does",()=>{
  const s=E.simulate(E.initial(),3);
  assert.equal(s.lost,true);
  assert.equal(s.won,false);
  assert.equal(s.moves,3);
  assert.deepEqual(asPlain(s.position),[2,0]);
  assert.equal(E.simulate(E.initial(),30).moves,3);
});

test("invalid edits are ignored and legal edits don't mutate their input",()=>{
  const initial=E.initial();
  assert.equal(E.edit(initial,[3,0],2),initial);
  assert.equal(E.edit(initial,[0,0],-1),initial);
  const edited=E.edit(initial,[1,0],8);
  assert.equal(edited.routes["1,0"],2);
  assert.equal(initial.routes["1,0"],0);
  assert.equal(Object.keys(edited.routes).length,19);
});

test("every attempted finite move remains in-bounds or explicitly loses",()=>{
  for(const p of E.CELLS) for(let d=0;d<6;d++){
    let s=E.initial();
    s={...s,position:asPlain(p),routes:{...s.routes,[E.key(p)]:d}};
    const result=E.step(s);
    assert.equal(result.moves,1);
    assert.ok(result.lost || E.inside(result.position));
    if(result.lost) assert.deepEqual(asPlain(result.position),asPlain(p));
  }
});


test("real UI script starts, accepts tap controls and completes animated demo",()=>{
  const ui=html.match(/<script id="hex-ui">([\s\S]*?)<\/script>/);
  assert.ok(ui);
  const all=new Map();
  const make=(id)=>({
    id,textContent:"",innerHTML:"",disabled:false,dataset:{},handlers:{},attrs:{},
    addEventListener(kind,fn){this.handlers[kind]=fn;},
    setAttribute(name,value){this.attrs[name]=value;},
    querySelectorAll(){return [];}
  });
  function get(id) {
    if(!all.has(id)) all.set(id,make(id));
    return all.get(id);
  }
  const buttons=Array.from({length:6},(_,i)=>{
    const el=make("dir"+i);el.dataset.dir=String(i);return el;
  });
  let currentTimer=null;
  const scope={
    globalThis:null,
    document:{
      getElementById:get,
      querySelectorAll(q){return q==="[data-dir]"?buttons:[];}
    },
    setInterval(fn){currentTimer=fn;return 1;},
    clearInterval(){currentTimer=null;}
  };
  scope.globalThis=scope;
  vm.runInNewContext(engine[1],scope,{timeout:3000});
  vm.runInNewContext(ui[1],scope,{timeout:3000});
  assert.equal(get("goals").textContent,"0 / 6");
  assert.equal(get("moves").textContent,"0 手");
  assert.match(get("board").innerHTML,/data-key="0,0"/);

  get("demo").handlers.click();
  assert.ok(currentTimer);
  for(let i=0;i<7;i++){
    const tick=currentTimer;
    assert.ok(tick);
    tick();
  }
  assert.equal(currentTimer,null);
  assert.equal(get("goals").textContent,"6 / 6");
  assert.equal(get("moves").textContent,"7 手");
  assert.match(get("message").textContent,/クリア/);
  assert.equal(get("step").disabled,true);

  get("reset").handlers.click();
  assert.equal(get("moves").textContent,"0 手");
  buttons[1].handlers.click();
  assert.equal(buttons[1].attrs["aria-pressed"],"true");
  get("step").handlers.click();
  assert.equal(get("moves").textContent,"1 手");
});
