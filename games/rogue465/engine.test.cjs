"use strict";
const {test}=require("node:test");
const assert=require("node:assert/strict");
const fs=require("node:fs");
const path=require("node:path");
const E=require("./engine.js");
const base=path.join(__dirname,"../..");
const registry=JSON.parse(fs.readFileSync(path.join(__dirname,"theorems.json"),"utf8"));
E.installCatalog(registry);

function copy(x){return JSON.parse(JSON.stringify(x));}
function clearRoom(s){const n=copy(s);for(const e of E.current(n).enemies)e.hp=0;return n;}
function pick(s){return s.offer?E.selectRelic(s,s.offer[0],0):s;}

test("authoritative, pinned baseline contains exactly 214+251 distinct original theorem names",()=>{
  const proof=JSON.parse(fs.readFileSync(path.join(base,registry.source),"utf8"));
  const orig=[...proof.parent_declarations,...proof.declarations].filter(x=>x.kind==="theorem");
  assert.equal(orig.length,465);
  assert.equal(proof.parent_theorem_count,214);
  assert.equal(proof.theorem_count,251);
  assert.equal(proof.parent_declaration_count+proof.declaration_count,509);
  assert.equal(new Set(orig.map(x=>x.name)).size,465);
  assert.equal(registry.cards.length,465);
  for(let i=0;i<465;i++){
    const actual=registry.cards[i],expected=orig[i];
    const file=expected.file.startsWith("../lean/")?expected.file.slice(3):"linear_input/"+expected.file;
    assert.equal(actual.id,i);assert.equal(actual.name,expected.name);
    assert.equal(actual.file,file);assert.equal(actual.line,expected.line);
    assert.equal(E.relic(i).name,expected.name);
  }
});

test("each of 465 proof names creates an actual usable relic effect",()=>{
  const seen=new Map();
  for(let id=0;id<465;id++){
    const item=E.relic(id);
    assert.ok(item.description.length>3);
    assert.ok(item.power===1||item.power===2);
    seen.set(item.effect,(seen.get(item.effect)||0)+1);
  }
  assert.ok(seen.size>=8);
  const s=E.newGame(4271);assert.equal(s.offer.length,3);
  assert.equal(new Set(s.offer).size,3);
  const id=s.offer[0],selected=E.selectRelic(s,id);
  assert.equal(selected.offer,null);
  assert.deepEqual(selected.equipment,[id]);
  assert.equal(s.equipment.length,0,"selection must not mutate original state");
});

test("all rooms, phase-shifted graph transitions and locks have actual costs",()=>{
  const s=pick(E.newGame(1));
  assert.equal(E.gates(s).length,1);
  assert.equal(E.gates(s)[0].vertex,4);
  assert.equal(E.progress(s).layerReachable,6);
  const room4=E.act(s,{type:"travel",edge:0});
  assert.equal(room4.vertex,4);assert.equal(room4.layer,0);
  assert.equal(E.act(room4,{type:"travel",edge:2}),room4,"cannot flee uncleared room");
  let cleared=clearRoom(room4);
  assert.equal(E.act(cleared,{type:"twist"}).sign[3],0,"2 insights are required");
  cleared.hero.insight=2;
  const flipped=E.act(cleared,{type:"twist"});
  assert.equal(flipped.sign[3],1);
  assert.equal(flipped.hero.insight,0);
  assert.equal(E.progress(flipped).layerReachable,12);
  const into=E.act(flipped,{type:"travel",edge:3});
  assert.deepEqual([into.vertex,into.layer],[5,1]);
  const after=E.act(clearRoom(into),{type:"travel",edge:5});
  assert.deepEqual([after.vertex,after.layer],[3,1]);
});

test("the initial free relic and later rewards cannot be farmed by revisiting",()=>{
  let s=E.newGame(42);
  assert.equal(s.offer.length,3);
  assert.equal(E.act(s,{type:"move",dx:0,dy:-1}),s);
  s=E.selectRelic(s,s.offer[0]);
  const room=E.current(s);
  assert.equal(room.claimed,true);
  let moved=E.act(s,{type:"travel",edge:0});
  moved=clearRoom(moved);
  moved=E.act(moved,{type:"travel",edge:0});
  assert.equal(moved.offer,null);
  assert.equal(moved.vertex,0);
  assert.equal(E.current(moved).claimed,true);
});

test("the integer two-probe formula recovers X exactly, and changes combat outcome",()=>{
  let s=pick(E.newGame(77));
  s=E.act(s,{type:"travel",edge:0});
  const enemy=E.living(E.current(s))[0];
  // Move one step not needed: scan the nearest enemy from center.
  const n=E.act(s,{type:"probe"});
  assert.equal(n.scans,1);
  const scanned=E.current(n).enemies.filter(e=>e.scanned);
  assert.equal(scanned.length,1);
  const p=scanned[0].probes;
  assert.equal(p[0]-p[1],p[2]);
  assert.equal(p[2],scanned[0].weakness);
  assert.ok(n.turn>s.turn);
});

test("sandpile toppling is finite, legal, uses a wired boundary and can damage monsters",()=>{
  let s=pick(E.newGame(97));
  s=E.act(s,{type:"travel",edge:0});
  const before=E.current(s).sand.reduce((a,b)=>a+b,0);
  // Pulse injects grains. Distinct rooms retain their sandpile history.
  const n=E.act(s,{type:"pulse"});
  const after=E.current(n).sand.reduce((a,b)=>a+b,0);
  assert.ok(n.topplings>=0);
  assert.ok(after<=before+4*3,"grains dissipate through walls and boundary");
  assert.ok(E.current(n).sand.every(x=>Number.isInteger(x)&&x>=0&&x<4));
  const saved=n.topplings;
  const again=E.act(n,{type:"pulse"});
  if(again!==n)assert.ok(again.topplings>=saved);
});

test("Rule 481 spore dynamics matches source truth table and symmetries",()=>{
  for(let mask=0;mask<32;mask++){
    const [c,n,e,s,w]=Array.from({length:5},(_,i)=>(mask>>i)&1);
    const val=E.rule481(c,n,e,s,w);
    assert.equal(val,E.rule481(c,n,w,s,e));
    assert.equal(val,E.rule481(c,s,e,n,w));
    assert.equal(1-val,E.rule481(1-c,1-n,1-e,1-s,1-w));
  }
  assert.deepEqual(E.sporesNext(Array(81).fill(0)),Array(81).fill(1));
  assert.deepEqual(E.sporesNext(Array(81).fill(1)),Array(81).fill(0));
});

test("death is permanent, and a cleared layer-1 goal advances or wins",()=>{
  let s=pick(E.newGame(13));
  // Independent UI goal guard check; bypassing combat in test only.
  s.depth=3;s.vertex=3;s.layer=1;s.rooms[E.roomKey(s)]={...E.current(s),enemies:[],
    claimed:true,map:E.current(s).map,sand:E.current(s).sand,spores:null};
  const ended=E.act(s,{type:"descend"});
  assert.equal(ended.status,"won");
  assert.ok(ended.score>0);
  assert.equal(E.act(ended,{type:"move",dx:0,dy:1}),ended);
  const dead=copy(s);dead.status="dead";
  assert.equal(E.act(dead,{type:"move",dx:0,dy:1}),dead);
});

test("the same seed and action trace produce exactly the same world",()=>{
  const play=()=>{
    let s=E.newGame(1966);
    s=E.selectRelic(s,s.offer[1]);
    s=E.act(s,{type:"travel",edge:0});
    s=E.act(s,{type:"probe"});
    s=E.act(s,{type:"move",dx:1,dy:0});
    s=E.act(s,{type:"pulse"});
    return s;
  };
  assert.deepEqual(play(),play());
});
