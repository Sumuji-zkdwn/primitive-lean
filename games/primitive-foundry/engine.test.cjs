"use strict";
const test=require("node:test");
const assert=require("node:assert/strict");
const fs=require("node:fs");
const path=require("node:path");
const F=require("./engine.js");
const T=JSON.parse(fs.readFileSync(path.join(__dirname,"tech.json"),"utf8"));
const E=JSON.parse(fs.readFileSync(path.join(__dirname,"../../docs/dependency/data/source_edges.json"),"utf8"));

test("research tree is a selected exact subgraph of actual aggregated proof references",()=>{
 const ids=new Map(T.nodes.map(t=>[t.id,t]));
 assert.equal(T.nodes.length,10);
 for(const t of T.nodes){
  assert.ok(ids.has(t.id));assert.ok(t.label.length>=2);
  for(const p of t.prerequisites){
   const origin=E.find(x=>x.source===t.path&&x.target===ids.get(p.id).path);
   assert.ok(origin,t.id+" missing actual proof edge "+p.id);
   assert.equal(origin.counts.proof,p.proofReferences);
  }
 }
 // Graph paths must not contain cycles.
 function walk(id,seen=[]){
   assert.ok(!seen.includes(id),"cycle "+[...seen,id].join(" -> "));
   ids.get(id).prerequisites.forEach(p=>walk(p.id,[...seen,id]));
 }
 T.nodes.forEach(t=>walk(t.id));
});

test("sample factory does real end-to-end mining, smelting, belts, assembly, lab and power",()=>{
 const w=F.newWorld(2026);
 F.demoBlueprint(w);
 const count=F.counts(w);
 assert.equal(count.miner,2);
 assert.equal(count.ironFurnace,1);
 assert.equal(count.copperFurnace,1);
 assert.equal(count.press,1);
 assert.equal(count.winder,1);
 assert.equal(count.assembler,1);
 assert.equal(count.lab,1);
 assert.equal(count.generator,1);
 const oreStart=w.tiles[F.idx(3,5)].qty;
 const copperStart=w.tiles[F.idx(3,11)].qty;
 F.advance(w,1200);
 console.log("FOUNDRY_DEMO",JSON.stringify({
  science:w.science,totalScience:w.totalScience,tick:w.tick,energy:w.energy,
  transported:w.transported,products:w.products,docs:w.documents,notes:w.notes.slice(0,3)
 }));
 assert.ok(w.totalScience>=10,"factory must create at least 10 actual science packs");
 assert.ok(w.products.circuit>=w.totalScience);
 assert.ok(w.products.gear>=w.totalScience);
 assert.ok(w.products.wire>=w.totalScience*2);
 assert.ok(w.tiles[F.idx(3,5)].qty<oreStart);
 assert.ok(w.tiles[F.idx(3,11)].qty<copperStart);
 assert.ok(w.transported>50);
 assert.ok(w.energy>=0);
 assert.ok(w.documents.includes("doc3")&&w.documents.includes("doc10"));
 assert.ok(w.tiles.every(x=>(!x.building||x.building.kind!=="belt"||
   x.building.item===null||F.ITEMS[x.building.item])));
});

test("belt transfers are deterministic and blocked belts never overwrite items",()=>{
 const w=F.newWorld(22);
 assert.ok(F.setMachine(w,8,8,"belt",0));
 assert.ok(F.setMachine(w,9,8,"belt",0));
 const one=w.tiles[F.idx(8,8)].building,two=w.tiles[F.idx(9,8)].building;
 one.item="ironOre";two.item="copperOre";
 F.advance(w,2);
 assert.equal(one.item,"ironOre");
 assert.equal(two.item,"copperOre");
 two.item=null;F.advance(w,2);
 assert.equal(one.item,null);
 assert.equal(two.item,"ironOre");
});

test("mining and electric generation require the corresponding ore patches",()=>{
 const w=F.newWorld(1);
 assert.equal(F.place(w,10,7,"miner",0),false);
 assert.equal(F.place(w,3,15,"miner",0),false);
 assert.equal(F.place(w,3,5,"generator",0),false);
 assert.equal(F.place(w,3,15,"generator",0),true);
 const reserve=w.tiles[F.idx(3,15)].qty;
 F.advance(w,40);
 assert.ok(w.tiles[F.idx(3,15)].qty<reserve);
 assert.ok(w.products.burnedCoal>=1);
});

test("technology unlocks are real gated costs, and the upgrades affect simulation rules",()=>{
 const w=F.newWorld(42),find=id=>T.nodes.find(x=>x.id===id);
 const fast=find("scaling"),heat=find("gradient"),power=find("gradientBound");
 assert.equal(F.unlock(w,fast),false);
 assert.equal(F.place(w,12,8,"junction",0),false);
 w.science=30;
 assert.equal(F.unlock(w,fast),true);
 assert.equal(F.unlock(w,fast),false,"cannot purchase twice");
 assert.ok(w.unlocks.includes("scaling"));
 assert.equal(F.unlock(w,heat),true);
 assert.equal(F.unlock(w,power),true);
 assert.equal(F.place(w,12,8,"junction",0),false);
 assert.equal(F.unlock(w,find("composition")),true);
 assert.equal(F.place(w,12,8,"junction",0),true);
 assert.ok(w.science<30);
});

test("machines do not produce parts without inputs, and power storage stays nonnegative",()=>{
 const w=F.newWorld(1);
 F.place(w,12,8,"assembler",0);
 F.place(w,13,8,"lab",0);
 w.energy=0;
 F.advance(w,80);
 assert.equal(w.totalScience,0);
 assert.equal(w.products.circuit,undefined);
 assert.equal(w.energy,0);
});

test("two worlds with the same layout and number of steps produce identical histories",()=>{
 const a=F.demoBlueprint(F.newWorld(17));
 const b=F.demoBlueprint(F.newWorld(17));
 F.advance(a,310);F.advance(b,310);
 assert.deepEqual(a,b);
});

test("research rewards advance into a fully operable early-game goal",()=>{
 const w=F.demoBlueprint(F.newWorld(95));
 F.advance(w,2400);
 assert.ok(w.totalScience>=30,"thirty science packs is reachable");
 assert.equal(w.status,"complete");
 assert.ok(w.documents.includes("doc25"));
});


test("actual recovered design document unlocks the eastern map and construction",()=>{
 const w=F.demoBlueprint(F.newWorld(19));
 assert.equal(F.isDiscovered(w,19,10),false);
 assert.equal(F.place(w,19,10,"belt",0),false);
 F.advance(w,1200);
 assert.ok(w.documents.includes("doc10"));
 assert.equal(F.isDiscovered(w,19,10),true);
 assert.equal(F.place(w,19,10,"belt",0),true);
});

test("a researched junction alternates output lanes without duplicating or losing items",()=>{
 const w=F.newWorld(21);
 w.unlocks.push("composition");
 assert.ok(F.setMachine(w,7,7,"junction",0));
 assert.ok(F.setMachine(w,8,7,"belt",0));
 assert.ok(F.setMachine(w,7,8,"belt",1));
 const j=w.tiles[F.idx(7,7)].building;
 assert.equal(F.inject(w,F.idx(7,7),"ironPlate"),true);
 assert.equal(F.inject(w,F.idx(7,7),"copperPlate"),true);
 assert.equal(F.inject(w,F.idx(7,7),"gear"),false,"splitter capacity must be bounded");
 F.advance(w,2);
 assert.equal(j.queue.length,0);
 assert.equal(w.tiles[F.idx(8,7)].building.item,"ironPlate");
 assert.equal(w.tiles[F.idx(7,8)].building.item,"copperPlate");
});

test("research tech is a source-backed prerequisite structure, not a random equipment name",()=>{
 const t=id=>T.nodes.find(x=>x.id===id);
 const w=F.newWorld(21);
 w.science=25;
 assert.equal(F.unlock(w,t("globalConsequences")),false);
 assert.equal(F.unlock(w,t("gradient")),true);
 assert.equal(F.unlock(w,t("gradientBound")),true);
 assert.equal(F.unlock(w,t("globalConsequences")),true);
 assert.equal(w.science,25-3-6-8);
 assert.equal(w.unlocks.includes("globalConsequences"),true);
});
