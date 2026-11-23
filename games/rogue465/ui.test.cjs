"use strict";
const {test}=require("node:test");
const assert=require("node:assert/strict");
const fs=require("node:fs");
const path=require("node:path");
const vm=require("node:vm");
const directory=__dirname;
const play=fs.readFileSync(path.join(directory,"play.html"),"utf8");
const engine=fs.readFileSync(path.join(directory,"engine.js"),"utf8");
const ui=fs.readFileSync(path.join(directory,"ui.js"),"utf8");
const registry=JSON.parse(fs.readFileSync(path.join(directory,"theorems.json"),"utf8"));

function readEmbedded(id){
  const re=new RegExp('<script[^>]*id="'+id+'"[^>]*>([\\s\\S]*?)<\\/script>');
  const m=play.match(re);
  assert.ok(m,"missing embedded "+id);
  return m[1];
}

test("offline page is actually self-contained and includes all 465 theorem declarations",()=>{
  assert.match(play,/name="viewport"/);
  assert.match(play,/id="rogue-catalog"/);
  assert.equal(JSON.parse(readEmbedded("rogue-catalog")).cards.length,465);
  assert.ok(play.includes(engine),"embedded engine is older than engine.js");
  assert.ok(play.includes("id=\"rogue-rot-vendor\""),"vendored roguelike toolkit must be bundled");
  assert.match(play,/Kenney Tiny Dungeon/);
  assert.ok(play.includes(ui),"embedded UI is older than ui.js");
  assert.equal((play.match(/<script src=/g)||[]).length,0);
  assert.equal((play.match(/<link[^>]*href="https?:/g)||[]).length,0);
  for(const id of ["board","gear","modal","gates","pulse","probe","polarity","twist","descend","hp"])
    assert.match(play,new RegExp('id="'+id+'"'));
});

test("offline browser starts with three genuine 465 relic choices and can move, fight, switch input",()=>{
  const elements=new Map();
  const moveControls=["0,-1","-1,0","0,1","1,0"].map(k=>element("move"+k,{move:k}));
  function element(id,dataset={}){
    const ev={},attrs={},set=new Set(),cache={};
    let lastMarkup=null;
    return {
      id,dataset,ev,attrs,textContent:"",innerHTML:"",disabled:false,
      classList:{add(k){set.add(k);},remove(k){set.delete(k);},contains(k){return set.has(k);}},
      addEventListener(name,fn){ev[name]=fn;},
      setAttribute(k,v){attrs[k]=v;},
      querySelectorAll(sel){
        if(this.innerHTML!==lastMarkup){for(const k of Object.keys(cache))delete cache[k];lastMarkup=this.innerHTML;}
        if(cache[sel])return cache[sel];
        const attr={"[data-x]":"x","[data-pick]":"pick","[data-slot]":"slot","[data-edge]":"edge"}[sel];
        if(!attr)return [];
        const matches=Array.from(this.innerHTML.matchAll(new RegExp('data-'+attr+'="([^"]+)"','g')));
        return (cache[sel]=matches.map((m,i)=>{
          const item=element(id+":"+attr+i,{[attr]:m[1]});
          if(attr==="x"){
            const tail=this.innerHTML.slice(m.index);
            const match=tail.match(/data-y="(\d+)"/);
            if(match)item.dataset.y=match[1];
          }
          return item;
        }));
      }
    };
  }
  function get(id){
    if(!elements.has(id))elements.set(id,element(id));
    return elements.get(id);
  }
  get("rogue-catalog").textContent=readEmbedded("rogue-catalog");
  const saved={};
  const sandbox={
    globalThis:null,
    document:{
      getElementById:get,
      querySelectorAll(selector){return selector==="[data-move]"?moveControls:[];},
      addEventListener(){}
    },
    localStorage:{
      getItem(k){return saved[k]||null;},
      setItem(k,v){saved[k]=v;}
    },
    confirm(){return true;},
    fetch(){throw Error("Offline page must not fetch network data")},
    Math,console,Date,JSON,
  };
  sandbox.globalThis=sandbox;
  const scripts=["rogue-rot-vendor","rogue-engine","rogue-ui"].map(readEmbedded);
  assert.equal(scripts.length,3);
  for(const script of scripts)vm.runInNewContext(script,sandbox,{timeout:5000});
  assert.ok(sandbox.ROT?.Path?.AStar,"the offline page uses vendored rot.js");
  assert.ok(sandbox.ROT?.FOV?.PreciseShadowcasting,"rot.js visibility is available");
  const S=sandbox.Rogue465;
  assert.equal(S.catalog().length,465);
  assert.equal(get("floor").textContent,"1 / 3");
  assert.equal(get("hp").textContent,"18 / 18");
  assert.equal(get("modal").classList.contains("visible"),true);
  const rewards=get("modal-panel").querySelectorAll("[data-pick]");
  assert.equal(rewards.length,3);
  rewards[0].ev.click();
  assert.equal(get("modal").classList.contains("visible"),false);
  const state=JSON.parse(saved["primitive-rogue465-save-v1"]);
  assert.equal(state.equipment.length,1);
  assert.equal(state.offer,null);
  assert.match(get("location").textContent,/部屋0/);
  const originalInput=state.hero.input;
  get("polarity").ev.click();
  const changed=JSON.parse(saved["primitive-rogue465-save-v1"]);
  assert.equal(changed.hero.input,-originalInput);
  moveControls[0].ev.click();
  const moved=JSON.parse(saved["primitive-rogue465-save-v1"]);
  assert.equal(moved.turn,1);
  assert.equal(moved.hero.y,3);
  get("pulse").ev.click();
  assert.ok(get("log").innerHTML.length>0);
  get("info").ev.click();
  assert.equal(get("modal").classList.contains("visible"),true);
  assert.ok(get("modal-panel").innerHTML.includes("遊び方"));
});
