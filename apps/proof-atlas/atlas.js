"use strict";
/* Primitive Atlas: truth layer = recorded theorem-reference DAG.
   Human exploratory links live separately and are never Lean proof edges. */
(function(root,factory){
 const api=factory();
 if(typeof module==="object"&&module.exports)module.exports=api;
 root.PrimitiveAtlas=api;
})(globalThis,function(){
 const SIZE=465,EDGES=629;
 const clamp=(n,a,b)=>Math.max(a,Math.min(b,n));
 function createModel(graph,sources,narratives){
  if(graph?.schema!==2||graph.nodes?.length!==SIZE||graph.summary?.proofEdges!==EDGES)
   throw Error("The original 465 theorem DAG is missing or inconsistent");
  if(sources?.records?.length!==SIZE)throw Error("All 465 source statements are mandatory");
  const nodes=graph.nodes.slice().sort((a,b)=>a.id-b.id);
  const proofs=sources.records.slice().sort((a,b)=>a.id-b.id);
  const nameToId=new Map(),children=Array.from({length:SIZE},()=>[]);
  let edges=0;
  for(let i=0;i<SIZE;i++){
   const n=nodes[i],p=proofs[i];
   if(n.id!==i||p.id!==i||!p.statement||!p.proof||!Number.isInteger(p.line))
    throw Error("Source statement and theorem graph disagree at "+i);
   if(nameToId.has(n.name))throw Error("Duplicate theorem: "+n.name);
   nameToId.set(n.name,i);
  }
  for(const n of nodes)for(const p of n.parents){
   if(!Number.isInteger(p)||p<0||p>=SIZE||nodes[p].depth>=n.depth)
    throw Error("Invalid DAG edge "+p+" -> "+n.id);
   children[p].push(n.id);edges++;
  }
  if(edges!==EDGES)throw Error("Unexpected count of direct proof references");
  const argumentsById={};
  for(const [name,arg] of Object.entries(narratives?.narratives||{})){
   if(!nameToId.has(name))throw Error("Human explanation lacks verified theorem: "+name);
   if(!arg.summary||!Array.isArray(arg.steps))throw Error("Incomplete human explanation");
   argumentsById[nameToId.get(name)]=arg;
  }
  const layers=new Map();
  for(const n of nodes){
   if(!layers.has(n.depth))layers.set(n.depth,[]);
   layers.get(n.depth).push(n);
  }
  for(const arr of layers.values())arr.sort((a,b)=>a.school.localeCompare(b.school)||a.chapter.localeCompare(b.chapter)||a.id-b.id);
  const overview=new Map();
  for(const [depth,arr] of layers)for(let i=0;i<arr.length;i++)
   overview.set(arr[i].id,{x:depth*185,y:i*32+(arr[i].school==="LinearInput"?3:0)});
  return {graph,nodes,proofs,argumentsById,children,nameToId,overview,layers};
 }
 const short=n=>n.label.replace(/\s*·\s*[0-9]{3}$/,"");
 function focus(model,selected,level=2){
  const positions=new Map([[selected,0]]),queue=[selected];
  for(let k=0;k<queue.length;k++){
   const id=queue[k],d=positions.get(id);
   if(Math.abs(d)>=level)continue;
   if(d<=0)for(const p of model.nodes[id].parents)if(!positions.has(p)){
    positions.set(p,d-1);queue.push(p);
   }
   if(d>=0)for(const c of model.children[id])if(!positions.has(c)){
    positions.set(c,d+1);queue.push(c);
   }
  }
  const cols=new Map();
  for(const [id,d] of positions){
   if(!cols.has(d))cols.set(d,[]);
   cols.get(d).push(id);
  }
  const pos=new Map();
  for(const [col,ids] of cols){
   ids.sort((a,b)=>model.nodes[a].chapter.localeCompare(model.nodes[b].chapter)||a-b);
   const step=Math.max(44,Math.min(58,700/Math.max(1,ids.length)));
   ids.forEach((id,i)=>pos.set(id,{x:col*225,y:(i-(ids.length-1)/2)*step}));
  }
  return pos;
 }
 function search(model,query,limit=36){
  const q=query.trim().toLowerCase();if(!q)return [];
  return model.nodes.map(n=>{
   const p=model.proofs[n.id],str=[n.label,n.chapter,n.name,"no."+String(n.id+1).padStart(3,"0"),p.comment].join(" ").toLowerCase();
   const score=String(n.id+1)===q||String(n.id+1).padStart(3,"0")===q?50:
    n.label.toLowerCase().includes(q)?40:n.name.toLowerCase().includes(q)?35:
    n.chapter.toLowerCase().includes(q)?25:str.includes(q)?20:p.statement.toLowerCase().includes(q)?10:0;
   return {id:n.id,score};
  }).filter(x=>x.score>0).sort((a,b)=>b.score-a.score||a.id-b.id).slice(0,limit);
 }
 function proofLineMatches(model,id,parentId){
  const parent=model.nodes[parentId],record=model.proofs[id];
  const stem=parent.name.split(".").at(-1),lines=record.proof.split("\n"),matches=[];
  lines.forEach((line,i)=>{if(line.includes(stem)||line.includes(parent.name))matches.push({line:i+1,text:line.trim()});});
  return matches.slice(0,5);
 }
 function addLink(model,links,from,to,note=""){
  if(!Number.isInteger(from)||!Number.isInteger(to)||from===to||from<0||to<0||from>=SIZE||to>=SIZE)throw Error("Invalid research link");
  if(links.some(x=>x.from===from&&x.to===to))return links;
  return [...links,{from,to,note:String(note).trim().slice(0,600)}];
 }
 function sanitizeLinks(model,links){
  if(!Array.isArray(links))return [];
  let result=[];
  for(const item of links.slice(0,300)){
   try{result=addLink(model,result,item.from,item.to,item.note);}catch(_){}
  }
  return result;
 }
 function descendants(model,start){
  const seen=new Set(),queue=[start];
  for(let i=0;i<queue.length;i++)for(const child of model.children[queue[i]])
   if(!seen.has(child)){seen.add(child);queue.push(child);}
  return seen.size;
 }
 return Object.freeze({SIZE,EDGES,clamp,createModel,short,focus,search,proofLineMatches,addLink,sanitizeLinks,descendants});
});
