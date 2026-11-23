"use strict";
const {test}=require("node:test");
const assert=require("node:assert/strict");
const fs=require("node:fs");
const path=require("node:path");
const ROT=require("./vendor/rot.min.js");
const E=require("./engine.js");
E.installCatalog(JSON.parse(fs.readFileSync(path.join(__dirname,"theorems.json"),"utf8")));
globalThis.ROT=ROT;

test("BSD-licensed vendor exposes precise shadowcasting and A* without a network request",()=>{
  assert.equal(typeof ROT.FOV.PreciseShadowcasting,"function");
  assert.equal(typeof ROT.Path.AStar,"function");
  const license=fs.readFileSync(path.join(__dirname,"vendor/rot.LICENSE.txt"),"utf8");
  assert.match(license,/Copyright \(c\) 2012-now\(\), Ondrej Zara/);
  assert.match(license,/Redistribution and use in source and binary forms/);
});

test("rot.js FOV reveals a near wall but not space immediately behind an opaque wall",()=>{
  const s=E.newGame(431);
  E.current(s).map=Array.from({length:81},(_,i)=>E.inside(i%9,Math.floor(i/9))?0:1);
  const wall=E.tile(4,3),hidden=E.tile(4,2);
  for(let x=1;x<8;x++) E.current(s).map[E.tile(x,3)]=1;
  const visible=E.visibleTiles(s,5);
  assert.ok(visible.includes(E.tile(s.hero.x,s.hero.y)));
  assert.ok(visible.includes(wall),"occluding wall should still be seen");
  assert.ok(!visible.includes(hidden),"horizontal wall should hide the cells behind it");
});

test("engine enemy phase uses the vendored rot.js A* while respecting solid tiles",()=>{
  let astarCalls=0;
  const original=ROT.Path.AStar;
  globalThis.ROT={...ROT,Path:{...ROT.Path,AStar:class extends original{
    constructor(...args){super(...args);astarCalls++;}
  }}};
  let s=E.newGame(431);s=E.selectRelic(s,s.offer[0]);
  const r=E.current(s);
  r.map=Array.from({length:81},(_,i)=>E.inside(i%9,Math.floor(i/9))?0:1);
  r.map[E.tile(4,5)]=1;
  r.enemies=[{id:0,kind:"guard",x:6,y:6,hp:14,maxHp:14,attack:1,
    scanned:false,windup:false,weakness:0}];
  // This is a legal game action; enemy movement occurs in the subsequent phase.
  const after=E.act(s,{type:"probe"});
  assert.ok(astarCalls>0,"the gameplay enemy must invoke rot.js A*");
  const next=E.living(E.current(after))[0];
  assert.ok(E.free(E.current(after),next.x,next.y));
  assert.ok(E.manhattan(next,s.hero)<E.manhattan(r.enemies[0],s.hero)||
    E.manhattan(next,r.enemies[0])===1,
    "the enemy should take one valid A* step around obstacles");
  globalThis.ROT=ROT;
});

test("original 465 theorem catalog remains unchanged by free art and path library",()=>{
  assert.equal(E.catalog().length,465);
  assert.equal(E.catalog().filter(x=>x.school==="Elastica").length,214);
  assert.equal(E.catalog().filter(x=>x.school==="LinearInput").length,251);
  const html=fs.readFileSync(path.join(__dirname,"index.html"),"utf8");
  assert.match(html,/Kenney Tiny Dungeon/);
  assert.match(html,/vendor\/rot\.min\.js/);
  assert.match(html,/kenney-sprite\.hero-art/);
  assert.match(html,/b3cbf86470ebdb68a80d48678db764dcaff181ac/);
});
