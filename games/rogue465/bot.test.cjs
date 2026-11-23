"use strict";
/* Basic independent hands-off smoke playthrough. It uses only public game
 * actions, never edits enemy life or teleport coordinates directly. */
const {test}=require("node:test");
const assert=require("node:assert/strict");
const fs=require("node:fs");
const path=require("node:path");
const E=require("./engine.js");
E.installCatalog(JSON.parse(fs.readFileSync(path.join(__dirname,"theorems.json"),"utf8")));

function choose(s){
  if(!s.offer)return s;
  const priority={force:9,guard:9,vital:9,siphon:7,ripple:6,focus:4,
    charge:5,pierce:5,stride:3,luck:2};
  const id=s.offer.slice().sort((a,b)=>priority[E.relic(b).effect]*
    E.relic(b).power-priority[E.relic(a).effect]*E.relic(a).power)[0];
  return E.selectRelic(s,id,0);
}
function pathDirection(s,target){
  const room=E.current(s),from=E.tile(s.hero.x,s.hero.y),dest=E.tile(target.x,target.y);
  const q=[from],parent=Array(81).fill(-1);parent[from]=from;
  for(let i=0;i<q.length;i++){
    const p=q[i];if(p===dest)break;
    for(const [dx,dy] of E.DIRS){
      const x=p%9+dx,y=Math.floor(p/9)+dy;
      if(!E.free(room,x,y))continue;
      const idx=E.tile(x,y);
      if(parent[idx]===-1){parent[idx]=p;q.push(idx);}
    }
  }
  if(parent[dest]===-1)return null;
  let step=dest;while(parent[step]!==from&&step!==from)step=parent[step];
  return {dx:step%9-s.hero.x,dy:Math.floor(step/9)-s.hero.y};
}
function killRoom(input){
  let s=choose(input);
  for(let t=0;t<300&&s.status==="play";t++){
    s=choose(s);
    const living=E.living(E.current(s));
    if(living.length===0)return s;
    living.sort((a,b)=>E.manhattan(s.hero,a)-E.manhattan(s.hero,b));
    const target=living[0],dist=E.manhattan(s.hero,target);
    if(!target.scanned && (target.kind==="warden"||target.hp>=7)&&dist<=4){
      s=E.act(s,{type:"probe"});continue;
    }
    if(s.hero.input*target.weakness<0)
      s=E.act(s,{type:"polarity"});
    if(s.hero.energy>=2 && ((living.length>=2 && dist<=3)||(dist<=3 && target.hp>E.stats(s).attack+2))){
      s=E.act(s,{type:"pulse"});continue;
    }
    if(dist===1){
      s=E.act(s,{type:"move",dx:target.x-s.hero.x,dy:target.y-s.hero.y});continue;
    }
    const d=pathDirection(s,target);
    if(!d)break;
    s=E.act(s,{type:"move",...d});
  }
  return s;
}
function walk(s,edge){
  if(s.status!=="play")return s;
  s=choose(s);
  if(E.hasEnemies(s))s=killRoom(s);
  if(s.status==="play"&&!E.hasEnemies(s))s=E.act(s,{type:"travel",edge});
  return s;
}
function run(seed){
  let s=E.newGame(seed);
  for(let depth=1;depth<=3&&s.status==="play";depth++){
    s=killRoom(s);if(s.status!=="play")break;
    s=walk(s,0);s=killRoom(s);if(s.status!=="play")break;
    if(s.hero.insight<2){
      s=walk(s,1);s=killRoom(s);if(s.status!=="play")break;
      s=walk(s,1);
    }
    s=E.act(choose(s),{type:"twist"});
    if(s.sign[3]!==1)throw Error("twist blocked after clearing the two starting branches");
    s=walk(s,3);s=killRoom(s);
    if(s.status!=="play")break;
    s=walk(s,5);s=killRoom(s);
    if(s.status!=="play")break;
    s=E.act(choose(s),{type:"descend"});
  }
  return {seed,status:s.status,depth:s.depth,turn:s.turn,kills:s.hero.kills,hp:s.hero.hp,
    relics:s.equipment.length,insight:s.hero.insight,log:s.log.slice(0,3)};
}
test("multiple procedural dungeon seeds admit legal progression, combat and topology alterations",()=>{
  const results=Array.from({length:12},(_,i)=>run(1000+i));
  console.log("ROGUE465_AUTOPLAY",JSON.stringify(results));
  assert.ok(results.every(r=>r.turn>0 && r.kills>=1));
  assert.ok(results.some(r=>r.depth>=2||r.status==="won"),
    "at least one unassisted gameplay route should reach level two");
});
