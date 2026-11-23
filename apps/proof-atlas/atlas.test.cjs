"use strict";
const {test}=require("node:test");
const assert=require("node:assert/strict");
const fs=require("node:fs");
const path=require("node:path");
const A=require("./atlas.js");
const load=name=>JSON.parse(fs.readFileSync(path.join(__dirname,name),"utf8"));
const graph=load("graph.json"),proofs=load("proofs.json"),narratives=load("narratives.json");
const model=A.createModel(graph,proofs,narratives);

test("all 465 true theorem nodes, 629 direct references, 60 source files and 100 Japanese explanations",()=>{
 assert.equal(model.nodes.length,465);
 assert.equal(model.proofs.length,465);
 assert.equal(model.children.reduce((sum,ls)=>sum+ls.length,0),629);
 assert.equal(new Set(model.nodes.map(n=>n.file)).size,60);
 assert.equal(Object.keys(model.argumentsById).length,100);
 assert.equal(model.nodes.filter(n=>n.parents.length===0).length,146);
 assert.equal(model.nodes.filter(n=>n.depth===12).length,1);
 assert.ok(model.proofs.every(p=>p.statement.startsWith("theorem ")||p.statement.includes(" theorem ")));
 assert.ok(model.proofs.every(p=>p.proof.length>0));
});

test("readable explanation is displayed only when authored and backed by source",()=>{
 const identified=model.nameToId.get("LinearInputObservation.recover_coordinate");
 assert.ok(Number.isInteger(identified));
 assert.match(model.argumentsById[identified].summary,/X|座標/);
 assert.match(model.proofs[identified].statement,/u ≠ v/);
 assert.match(model.proofs[identified].proof,/ring/);
 const random=model.nodes.find(n=>model.argumentsById[n.id]===undefined);
 assert.ok(random);
 assert.ok(model.proofs[random.id].statement);
});

test("the focused proof graph navigates actual parents and downstream consequences",()=>{
 const id=model.nameToId.get("LinearInputObservation.two_inputs_iff_pair");
 const p=model.nodes[id].parents;
 assert.equal(p.length,3);
 const view=A.focus(model,id);
 assert.ok(view.has(id));
 for(const parent of p){assert.ok(view.has(parent));assert.ok(view.get(parent).x<view.get(id).x);}
 for(const next of model.children[id])assert.ok(view.has(next));
 assert.ok(model.overview.size===465);
 const refer=A.proofLineMatches(model,id,p[0]);
 assert.ok(refer.some(x=>x.text.length>0));
});

test("every edge follows a strictly increasing topological depth",()=>{
 for(const n of model.nodes)for(const id of n.parents)
  assert.ok(model.nodes[id].depth<n.depth,"unverified cycle in proof edges");
 assert.ok(A.descendants(model,225)>=0);
});

test("search finds Japanese chapter, theorem numbers and formal names",()=>{
 assert.ok(A.search(model,"曲率",40).length>3);
 assert.equal(A.search(model,"230")[0].id,229);
 assert.equal(A.search(model,"two_inputs_iff_pair")[0].id,229);
 assert.ok(A.search(model,"No.230").some(x=>x.id===229));
 assert.deepEqual(A.search(model,""),[]);
});

test("user conceptual links cannot mutate the canonical kernel-accepted DAG",()=>{
 const source=225,target=101,before=model.nodes[source].parents.slice();
 let links=A.addLink(model,[],source,target,"観測と幾何を比較する仮説");
 assert.equal(links.length,1);
 assert.equal(links[0].note,"観測と幾何を比較する仮説");
 links=A.addLink(model,links,source,target,"duplicate");
 assert.equal(links.length,1);
 assert.deepEqual(model.nodes[source].parents,before);
 assert.ok(!model.nodes[source].parents.includes(target));
 assert.throws(()=>A.addLink(model,links,source,source));
 const sanitized=A.sanitizeLinks(model,[...links,{from:-2,to:5,note:"invalid"},links[0]]);
 assert.equal(sanitized.length,1);
});

test("all extracted proof fragments are in ten original source batches",()=>{
 const batches=["elastica-0","elastica-1","elastica-2","elastica-3",
   "linearinput-0","linearinput-1","linearinput-2","linearinput-3","linearinput-4","linearinput-5"];
 const byId=new Map();
 for(const batch of batches){
  const data=load("data/"+batch+".json");
  for(const record of data.records){
   assert.ok(!byId.has(record.id));byId.set(record.id,record);
  }
 }
 assert.equal(byId.size,465);
 for(const p of model.proofs)assert.deepEqual(p,byId.get(p.id));
});

test("all 465 expansion plans are complete, unique and topological",()=>{
 for(const n of model.nodes){
  const order=A.proofOrder(model,[n.id]);
  assert.equal(new Set(order).size,order.length);
  assert.equal(order.at(-1),n.id);
  const independent=new Set([n.id]),pending=[n.id];
  while(pending.length)for(const p of model.nodes[pending.pop()].parents)if(!independent.has(p)){independent.add(p);pending.push(p);}
  assert.deepEqual(new Set(order),independent);
  for(const id of order)for(const p of model.nodes[id].parents)assert.ok(order.indexOf(p)<order.indexOf(id));
  const packet=A.argumentPacket(model,n.id);
  assert.ok(packet.includes(model.proofs[n.id].statement));
  assert.ok(packet.includes(model.proofs[n.id].proof));
  for(const p of n.parents)assert.ok(packet.includes(model.proofs[p].proof));
 }
 assert.throws(()=>A.proofOrder(model,[-1]));
});
test("human explanations cover the design-observation-calculus cluster",()=>{
 for(let id=214;id<=240;id++){
  const a=model.argumentsById[id];
  assert.ok(a?.title&&a?.summary&&a?.assumptions&&a?.steps.length>=2,"missing "+id);
 }
});

test("research packet distinguishes user conjecture from exact source, deduplicates theorem ids and preserves graph",()=>{
 const before=JSON.stringify(graph);
 const draft=A.sanitizeResearch(model,{ids:[225,226,229,229,-1,"227",465],claim:"二観測に制限したときの追加条件"});
 assert.deepEqual(draft.ids,[225,226,229]);
 const packet=A.researchPacket(model,draft,[{from:225,to:229,note:"比較仮説"}]);
 assert.match(packet,/未検証の研究構想/);
 assert.match(packet,/比較仮説/);
 assert.match(packet,/証明済みではない/);
 assert.match(packet,/実際に検証/);
 for(const id of draft.ids)assert.ok(packet.includes(proofs.records[id].proof));
 assert.ok(packet.includes(proofs.records[227].proof));
 assert.equal(JSON.stringify(graph),before);
 assert.equal(A.sanitizeResearch(model,{ids:model.nodes.map(x=>x.id),claim:"x".repeat(4000)}).ids.length,20);
 assert.equal(A.sanitizeResearch(model,{claim:"x".repeat(4000)}).claim.length,3000);
});

test("completed explanation chapters cover all geometry, reconstruction, scaling and energy coercivity records",()=>{
 const blocks=[[0,16],[95,113],[138,146],[152,163],[214,251]];
 for(const [a,b] of blocks)for(let id=a;id<=b;id++){
  const n=model.nodes[id],e=model.argumentsById[id];
  assert.ok(e?.title&&e?.assumptions&&e?.summary&&e?.steps?.length>=2,"missing "+n.name);
 }
});
