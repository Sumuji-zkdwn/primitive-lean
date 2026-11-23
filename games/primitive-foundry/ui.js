"use strict";
(async function(){
 const F=globalThis.PrimitiveFoundry;
 if(!F)throw Error("Factory engine not found");
 const $=id=>document.getElementById(id);
 const esc=s=>String(s).replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
 const techSource=$("factory-tech")?.textContent;
 const tech=techSource?JSON.parse(techSource):await (await fetch("./tech.json")).json();
 const upgradeSource=$("factory-upgrades-json")?.textContent;
 const upgrades=upgradeSource?JSON.parse(upgradeSource):await (await fetch("./upgrades.json")).json();
 if(tech.nodes.length!==465||tech.summary.proofEdges!==629)throw Error("465定理の依存台帳が不正です");
 const deepLinkView=typeof globalThis.location?.search==="string"&&
    typeof URLSearchParams==="function"?new URLSearchParams(globalThis.location.search).get("view"):null;
 const knownTech=new Map(upgrades.nodes.map(t=>[t.id,t]));
 const proofById=new Map(tech.nodes.map(t=>[t.id,t]));
 const proofByName=new Map(tech.nodes.map(t=>[t.name,t]));
 const proofChildren=new Map(tech.nodes.map(t=>[t.id,[]]));
 for(const node of tech.nodes)for(const parent of node.parents)proofChildren.get(parent).push(node.id);
 const byDepth=new Map();
 for(const node of tech.nodes)(byDepth.get(node.depth)||byDepth.set(node.depth,[]).get(node.depth)).push(node);
 const proofCoordinates=new Map();
 for(const [depth,arr] of byDepth){
  arr.sort((a,b)=>a.school.localeCompare(b.school)||a.chapter.localeCompare(b.chapter)||a.id-b.id);
  arr.forEach((n,i)=>proofCoordinates.set(n.id,{x:45+depth*210,y:38+i*26}));
 }
 const tools={
  logistics:[
   ["pan","調べる","⌖"],["belt","ベルト","»"],["miner","採掘機","◉"],
   ["junction","分配器","⑂","composition"],["rotate","回転","↻"],["erase","撤去","×"]
  ],
  production:[
   ["ironFurnace","鉄の炉","▤"],["copperFurnace","銅の炉","▤"],
   ["press","プレス","⌑"],["winder","巻線機","◎"],
   ["assembler","組立機","▣"],["lab","研究所","⌬"]
  ],
  utility:[["generator","発電機","◈"],["pan","調べる","⌖"],["rotate","回転","↻"],["erase","撤去","×"]]
 };
 const canvas=$("factory-canvas"),viewport=$("viewport"),ctx=canvas.getContext("2d");
 const proofCanvas=$("proof-graph"),proofCtx=proofCanvas?.getContext?.("2d")||null;
 if(!ctx){$("status").textContent="Canvas描画を利用できません。";return;}
 const STORAGE="primitive-foundry-save-v2";
 let world=null,category="logistics",tool="pan",dir=0,zoom=1;
 let pane="inspect",mobileScreen="factory",selected=null,clock=null,speed=1,touch=null,lastSave=0,helpOpen=false;
 const mapPointers=new Map();let mapPinch=null;
 const mobileScreens=["factory","build","inspect","research","documents"];
 let selectedProof=0,proofStatus="ready",proofSchool="all",proofSearch="";
 let graphMode="focus",graphShift={x:0,y:0},graphPointer=null,graphZoom=1;
 const graphPointers=new Map();let graphPinch=null;
 let graphHitboxes=[];
 let camX=typeof window!=="undefined"&&window.innerWidth<750?9.3:11.8,camY=8.4;
 let layoutW=700,layoutH=520,dpr=1;
 function load(){
  try{
   const s=localStorage.getItem(STORAGE),j=JSON.parse(s);
   if(j?.schema===1&&j.tiles?.length===F.SIZE&&Array.isArray(j.unlocks)&&
      Array.isArray(j.documents)&&typeof j.tick==="number")return j;
  }catch(_){}
  return null;
 }
 function persist(){
  try{localStorage.setItem(STORAGE,JSON.stringify(world));}catch(_){}
 }
 world=load()||F.challengeBlueprint(F.newWorld(20261124));
 if(!Array.isArray(world.proofs))world.proofs=[];
 if(!Array.isArray(world.proofNames))world.proofNames=[];
 if(world.status==="paused")world.status="playing";
 const tipBase="タップで配置・調査。ベルトはドラッグで敷設。地図を動かすには「調べる」を選びドラッグ。";
 function announce(msg){
  $("status").textContent=msg;
 }
 function resize(){
  const b=viewport.getBoundingClientRect();
  layoutW=Math.max(100,b.width);layoutH=Math.max(100,b.height);
  dpr=Math.min(2,globalThis.devicePixelRatio||1);
  canvas.width=Math.max(1,Math.round(layoutW*dpr));
  canvas.height=Math.max(1,Math.round(layoutH*dpr));
  canvas.style.width=layoutW+"px";
  canvas.style.height=layoutH+"px";
  draw();
 }
 function tileSize(){return (layoutW<680?35:31)*zoom;}
 function worldToScreen(x,y){
  const unit=tileSize();
  return [layoutW/2+(x-camX)*unit,layoutH/2+(y-camY)*unit];
 }
 function screenToWorld(sx,sy){
  const unit=tileSize();
  const x=Math.floor((sx-layoutW/2)/unit+camX);
  const y=Math.floor((sy-layoutH/2)/unit+camY);
  return F.inside(x,y)?{x,y}:null;
 }
 function drawPoly(points,color,stroke=null,width=1){
  ctx.beginPath();points.forEach(([x,y],i)=>i?ctx.lineTo(x,y):ctx.moveTo(x,y));
  ctx.closePath();ctx.fillStyle=color;ctx.fill();
  if(stroke){ctx.strokeStyle=stroke;ctx.lineWidth=width;ctx.stroke();}
 }
 function resourceSprite(tile,X,Y,s){
  const ore=tile.ore;
  if(!ore||tile.qty<=0)return;
  const color=ore==="ironOre"?"#a0c3ce":ore==="copperOre"?"#d89469":"#505b6a";
  ctx.fillStyle="#121d21aa";ctx.fillRect(X+2,Y+2,s-4,s-4);
  for(let a=0;a<4;a++){
   const n=(tile.tone*7+a*13+11)%17,k=(tile.tone*19+a*5)%17;
   const px=X+s*(.13+n/26),py=Y+s*(.13+k/26),z=s*(.1+.015*(a%3));
   drawPoly([[px,py-z],[px+z*.8,py-z*.1],[px+z*.5,py+z],[px-z*.6,py+z*.2]],
    color,"#182a34",Math.max(.7,s*.018));
  }
 }
 function itemDot(item,x,y,r){
  const info=F.ITEMS[item]||{color:"#fff"};
  ctx.fillStyle="#101b23";ctx.beginPath();ctx.arc(x,y,r+1,0,Math.PI*2);ctx.fill();
  ctx.fillStyle=info.color;ctx.beginPath();ctx.arc(x,y,r,0,Math.PI*2);ctx.fill();
 }
 function machineIcon(m,X,Y,s,tick){
  const colors={
   miner:["#3f6172","#97c0c9"],ironFurnace:["#6b5347","#ffd2a3"],
   copperFurnace:["#6b493c","#f4ad6e"],press:["#505d65","#cfd1c7"],
   winder:["#5e5352","#e6b46b"],assembler:["#395f5a","#83d8b4"],
   lab:["#3b5d70","#8fd8e5"],generator:["#58624b","#d4d999"],
   junction:["#526c69","#aed7d1"]
  };
  const [base,bright]=colors[m.kind]||colors.press;
  const cx=X+s/2,cy=Y+s/2;
  ctx.fillStyle="#0c1922";ctx.fillRect(X+s*.08,Y+s*.1,s*.84,s*.8);
  ctx.fillStyle=base;ctx.fillRect(X+s*.13,Y+s*.13,s*.74,s*.7);
  ctx.strokeStyle="#85969a";ctx.lineWidth=Math.max(.7,s*.04);
  ctx.strokeRect(X+s*.16,Y+s*.16,s*.68,s*.64);
  const glow=m.active?bright:"#728a8d";
  if(m.kind==="miner"){
   ctx.strokeStyle=glow;ctx.lineWidth=s*.075;
   ctx.beginPath();ctx.arc(cx,cy,s*.21,0,Math.PI*2);ctx.stroke();
   for(let k=0;k<6;k++){
    const a=(k/6)*Math.PI*2+(m.active?tick*.05:0);
    ctx.beginPath();ctx.moveTo(cx+Math.cos(a)*s*.14,cy+Math.sin(a)*s*.14);
    ctx.lineTo(cx+Math.cos(a)*s*.29,cy+Math.sin(a)*s*.29);ctx.stroke();
   }
   ctx.fillStyle=bright;ctx.fillRect(cx-s*.05,cy-s*.05,s*.1,s*.1);
  }else if(m.kind==="ironFurnace"||m.kind==="copperFurnace"){
   ctx.fillStyle="#171b21";ctx.fillRect(cx-s*.24,cy-s*.22,s*.48,s*.45);
   ctx.fillStyle=glow;ctx.fillRect(cx-s*.18,cy-s*.12,s*.36,s*.26);
   ctx.fillStyle="#25272a";ctx.fillRect(cx+s*.12,cy-s*.29,s*.16,s*.2);
   ctx.fillStyle="#111c23";ctx.fillRect(cx-s*.3,cy+s*.16,s*.6,s*.07);
  }else if(m.kind==="press"){
   ctx.fillStyle=glow;ctx.fillRect(cx-s*.26,cy-s*.18,s*.52,s*.12);
   ctx.fillRect(cx-s*.3,cy+s*.15,s*.6,s*.13);
   ctx.fillStyle="#263842";ctx.fillRect(cx-s*.08,cy-s*.1,s*.16,s*.25);
  }else if(m.kind==="winder"){
   ctx.strokeStyle=glow;ctx.lineWidth=s*.09;
   ctx.beginPath();ctx.arc(cx,cy,s*.18,0,Math.PI*2);ctx.stroke();
   ctx.beginPath();ctx.arc(cx,cy,s*.08,0,Math.PI*2);ctx.stroke();
   ctx.fillStyle="#182732";ctx.fillRect(cx-s*.25,cy+s*.2,s*.5,s*.07);
  }else if(m.kind==="assembler"){
   ctx.fillStyle="#142d30";ctx.fillRect(cx-s*.2,cy-s*.2,s*.4,s*.4);
   ctx.strokeStyle=glow;ctx.lineWidth=s*.075;ctx.strokeRect(cx-s*.15,cy-s*.15,s*.3,s*.3);
   for(const [dx,dy]of [[-.24,0],[.24,0],[0,-.24],[0,.24]]){
    ctx.fillStyle=glow;ctx.fillRect(cx+dx*s-s*.045,cy+dy*s-s*.045,s*.09,s*.09);
   }
  }else if(m.kind==="lab"){
   ctx.strokeStyle=glow;ctx.lineWidth=s*.065;
   ctx.beginPath();ctx.arc(cx,cy,s*.23,0,Math.PI*2);ctx.stroke();
   ctx.fillStyle="#102836";ctx.beginPath();ctx.arc(cx,cy,s*.12,0,Math.PI*2);ctx.fill();
   ctx.fillStyle=glow;ctx.beginPath();ctx.arc(cx,cy,s*.055,0,Math.PI*2);ctx.fill();
  }else if(m.kind==="generator"){
   ctx.fillStyle="#243330";ctx.fillRect(cx-s*.22,cy-s*.2,s*.44,s*.4);
   ctx.strokeStyle=glow;ctx.lineWidth=s*.07;
   for(let k=-1;k<=1;k++){
    ctx.beginPath();ctx.moveTo(cx+k*s*.12,cy-s*.2);ctx.lineTo(cx+k*s*.12,cy+s*.2);ctx.stroke();
   }
   ctx.fillStyle=glow;ctx.fillRect(cx+s*.26,cy-s*.24,s*.06,s*.13);
  }else{
   ctx.strokeStyle=glow;ctx.lineWidth=s*.06;
   ctx.beginPath();ctx.moveTo(cx-s*.2,cy);ctx.lineTo(cx,cy);ctx.lineTo(cx+s*.2,cy-s*.16);
   ctx.moveTo(cx,cy);ctx.lineTo(cx+s*.2,cy+s*.16);ctx.stroke();
  }
  // Paint the actual machine's output direction independently of its icon.
  const dx=F.DX[m.dir],dy=F.DY[m.dir];
  ctx.fillStyle=m.blocked?"#f0a480":"#f5e4ad";
  const px=cx+dx*s*.34,py=cy+dy*s*.34;
  drawPoly([[px+dx*s*.11,py+dy*s*.11],
    [px-dy*s*.065,py+dx*s*.065],
    [px+dy*s*.065,py-dx*s*.065]],ctx.fillStyle);
  if(m.queue.length)itemDot(m.queue[0],cx-s*.31,cy+s*.27,s*.075);
  if(m.progress){
   const ratio=Math.min(1,m.progress/(F.MACHINES[m.kind]?.period||1));
   ctx.fillStyle="#13202c";ctx.fillRect(X+s*.14,Y+s*.87,s*.72,s*.05);
   ctx.fillStyle=bright;ctx.fillRect(X+s*.14,Y+s*.87,s*.72*ratio,s*.05);
  }
 }
 function beltSprite(m,X,Y,s,time){
  ctx.fillStyle="#152329";ctx.fillRect(X+1,Y+1,s-2,s-2);
  ctx.save();ctx.translate(X+s/2,Y+s/2);ctx.rotate(m.dir*Math.PI/2);
  ctx.fillStyle="#263d46";ctx.fillRect(-s*.45,-s*.29,s*.9,s*.58);
  ctx.fillStyle="#46636d";ctx.fillRect(-s*.43,-s*.3,s*.86,s*.07);ctx.fillRect(-s*.43,s*.23,s*.86,s*.07);
  ctx.fillStyle="#c7ac76";
  const offset=(time*.04)%(.38*s);
  for(let k=-1;k<=2;k++){
   const px=-s*.5+k*s*.38+offset;
   ctx.beginPath();
   ctx.moveTo(px-s*.06,-s*.15);ctx.lineTo(px+s*.07,0);ctx.lineTo(px-s*.06,s*.15);
   ctx.lineWidth=Math.max(.6,s*.055);ctx.strokeStyle="#d4b97f";ctx.stroke();
  }
  if(m.item)itemDot(m.item,0,0,s*.15);
  ctx.restore();
 }
 function draw(){
  if(!world)return;
  ctx.setTransform(dpr,0,0,dpr,0,0);
  ctx.fillStyle="#10191f";ctx.fillRect(0,0,layoutW,layoutH);
  const s=tileSize();
  const ox=layoutW/2-camX*s,oy=layoutH/2-camY*s;
  const firstX=Math.max(0,Math.floor(-ox/s)-1),lastX=Math.min(F.W-1,Math.ceil((layoutW-ox)/s));
  const firstY=Math.max(0,Math.floor(-oy/s)-1),lastY=Math.min(F.H-1,Math.ceil((layoutH-oy)/s));
  ctx.save();ctx.beginPath();ctx.rect(0,0,layoutW,layoutH);ctx.clip();
  for(let y=firstY;y<=lastY;y++)for(let x=firstX;x<=lastX;x++){
   const tile=world.tiles[F.idx(x,y)],X=ox+x*s,Y=oy+y*s;
   const known=F.isDiscovered(world,x,y);
   if(!known){
    ctx.fillStyle=(x+y)%2?"#132028":"#111c24";ctx.fillRect(X,Y,s+.4,s+.4);
    if((x+y)%5===0){
     ctx.strokeStyle="#2b3d49";ctx.lineWidth=1;
     ctx.beginPath();ctx.moveTo(X+s*.22,Y+s*.15);ctx.lineTo(X+s*.7,Y+s*.65);ctx.stroke();
    }
    continue;
   }
   if(tile.ground==="water"){
    ctx.fillStyle=(tile.tone%3===0?"#183844":"#16303d");ctx.fillRect(X,Y,s+.3,s+.3);
    ctx.strokeStyle="#27606d";ctx.lineWidth=s*.028;
    ctx.beginPath();ctx.moveTo(X+s*.12,Y+s*.57);ctx.lineTo(X+s*.7,Y+s*.57);ctx.stroke();
   }else{
    ctx.fillStyle=tile.tone%7===0?"#2b3939":tile.tone%3===0?"#2e3b3a":"#293637";
    ctx.fillRect(X,Y,s+.3,s+.3);
    ctx.strokeStyle="#52605733";ctx.lineWidth=1;
    ctx.strokeRect(X+.5,Y+.5,s-.7,s-.7);
    if(tile.tone%7===2){
     ctx.fillStyle="#9f9b6638";ctx.fillRect(X+s*.19,Y+s*.75,s*.08,s*.08);
    }
   }
   resourceSprite(tile,X,Y,s);
   if(tile.building){
    const m=tile.building;
    if(m.kind==="belt")beltSprite(m,X,Y,s,world.tick);
    else machineIcon(m,X,Y,s,world.tick);
   }
   const repair=F.pendingRepairs(world).find(p=>p.x===x&&p.y===y);
   if(repair){
    ctx.save();ctx.setLineDash([3,3]);ctx.lineWidth=Math.max(2,s*.07);
    ctx.strokeStyle="#ffe19a";ctx.strokeRect(X+s*.09,Y+s*.09,s*.82,s*.82);
    ctx.fillStyle="#ffe19a";ctx.font="700 "+Math.max(12,Math.round(s*.4))+"px system-ui";
    ctx.textAlign="center";ctx.fillText(F.DIR_SYM[repair.dir],X+s*.5,Y+s*.62);
    ctx.restore();
   }
   if(selected?.x===x&&selected?.y===y){
    ctx.strokeStyle="#e6d09c";ctx.lineWidth=Math.max(1.5,s*.057);
    ctx.strokeRect(X+1,Y+1,s-2,s-2);
   }
  }
  // Frontier markings are gameplay information, not a UI cover obscuring controls.
  if(!world.documents.includes("doc10")&&!world.unlocks.includes("reconstruction")){
   const fx=ox+17*s;
   if(fx>=0&&fx<layoutW){
    ctx.save();ctx.setLineDash([5,5]);ctx.strokeStyle="#cead7799";ctx.lineWidth=2;
    ctx.beginPath();ctx.moveTo(fx,0);ctx.lineTo(fx,layoutH);ctx.stroke();ctx.restore();
    ctx.fillStyle="#c8b38c";ctx.font="600 10px system-ui";
    ctx.fillText("未解読区域",Math.max(12,fx+8),18);
   }
  }
  ctx.restore();
 }
 function setTool(next){
  tool=next;
  const def=Object.values(tools).flat().find(t=>t[0]===next);
  $("selected-tool").textContent=def?.[1]||"調べる";
  $("tip").textContent=next==="pan"?(F.pendingRepairs(world).length?"光る欠損セルをタップして搬送路を補修。ドラッグで地図を移動。":"建物をタップして調査。ドラッグで地図を動かします。"):
    next==="belt"?"画面をなぞるとベルトを連続敷設。向きも自動でつながります。":
    next==="rotate"?"向きを変えたい建物をタップしてください。":
    next==="erase"?"撤去したい装置をタップしてください。":
    (F.MACHINES[next]?.hint||tipBase);
  renderPalette();
 }
 function renderPalette(){
  const list=tools[category];
  $("tools").innerHTML=list.map(([id,label,icon,requires])=>{
   const locked=requires&&!world.unlocks.includes(requires);
   return '<button class="tool '+(locked?"locked":"")+'" data-tool="'+id+
    '" type="button" aria-pressed="'+(tool===id)+'" '+(locked?"disabled":"")+
    ' title="'+esc(locked?"要研究："+knownTech.get(requires)?.label:label)+'">'+
    '<span class="pict">'+esc(icon)+'</span><span class="caption">'+esc(label)+'</span></button>';
  }).join("");
  $("tools").querySelectorAll("[data-tool]").forEach(el=>el.addEventListener("click",()=>
    setTool(el.dataset.tool)));
  document.querySelectorAll("[data-category]").forEach(el=>
    el.setAttribute("aria-selected",String(el.dataset.category===category)));
  $("build-direction").textContent="方向 "+F.DIR_SYM[dir];
 }
 function setMobileScreen(next,preserveDeepLink=false){
  if(!mobileScreens.includes(next))return;
  mobileScreen=next;
  if(!preserveDeepLink)document.body?.classList?.remove("research-direct");
  for(const name of mobileScreens)document.body?.classList?.toggle("mobile-screen-"+name,name===next);
  document.querySelectorAll("[data-mobile-screen]").forEach(el=>
    el.setAttribute("aria-current",el.dataset.mobileScreen===next?"page":"false"));
  showPane(["research","documents","inspect"].includes(next)?next:"inspect");
  if(next==="factory"||next==="build"){
    if(typeof requestAnimationFrame==="function")requestAnimationFrame(()=>resize());
    else resize();
  }
  if(typeof window!=="undefined"&&typeof window.scrollTo==="function")window.scrollTo(0,0);
 }
 function showPane(id){
  pane=id;
  for(const x of ["inspect","research","documents"])$("view-"+x).classList.toggle("active",x===id);
  document.querySelectorAll("[data-panel]").forEach(el=>
    el.setAttribute("aria-selected",String(el.dataset.panel===id)));
  if(id==="research"){renderProof(true);renderTech();}
 }
 function renderInspector(){
  const div=$("inspector");
  if(!selected){div.textContent="工場の装置をタップすると、入力品目・出力方向・処理状況が分かります。";return;}
  const {x,y}=selected,m=F.machineStatus(world,x,y);
  if(!m){div.textContent="マップの外です。";return;}
  const rows=[["座標",x+", "+y],["地形",m.ore?F.ITEMS[m.ore]?.label||"石炭":"建設地"]];
  if(m.qty>0)rows.push(["埋蔵量",m.qty+""]);
  if(m.kind){
   rows.push(["装置",m.label],["向き",F.DIR_SYM[m.dir]],
    ["状態",m.blocked?"搬送が詰まっています":m.active?"稼働中":"待機中"],
    ["製造した個数",m.processed]);
   for(const [item,count] of Object.entries(m.stock||{}))if(count>0)
    rows.push(["投入 "+(F.ITEMS[item]?.label||item),count]);
   if(m.output?.length)rows.push(["出力待ち",m.output.map(x=>F.ITEMS[x]?.label||x).join(" / ")]);
   if(m.item)rows.push(["ベルト上",F.ITEMS[m.item]?.label||m.item]);
   rows.push(["機械説明",m.hint]);
  }
  div.innerHTML='<div class="inspectTitle">'+esc(m.kind?m.label:"建設用地")+"</div>"+
   rows.map(([k,v])=>'<div class="item"><span>'+esc(k)+'</span><strong>'+esc(v)+'</strong></div>').join("");
  $("rotate-selected").disabled=!m.kind;
  $("delete-selected").disabled=!m.kind;
 }
 function hasProof(node){return world.proofs.includes(node.id);}
 function proofReady(node){return !hasProof(node)&&node.parents.every(id=>world.proofs.includes(id));}
 function proofStatusOf(node){return hasProof(node)?"studied":proofReady(node)?"ready":"locked";}
 function proofStateLabel(node){
  return hasProof(node)?"研究済":proofReady(node)?"研究可能":"前提待ち";
 }
 function selectProof(id){
  if(!proofById.has(id))return;
  selectedProof=id;graphMode="focus";graphShift={x:0,y:0};graphZoom=1;
  renderProof(true);drawProofGraph();
 }
 function localProofPositions(){
  const center=proofById.get(selectedProof);
  const cols=new Map([[-2,[]],[-1,[]],[0,[center.id]],[1,[]],[2,[]]]);
  const parents=center.parents,children=proofChildren.get(center.id)||[];
  cols.set(-1,parents.slice());
  cols.set(1,children.slice());
  const grandParents=new Set(),grandChildren=new Set();
  for(const id of parents)for(const k of proofById.get(id).parents)if(!parents.includes(k))grandParents.add(k);
  for(const id of children)for(const k of proofChildren.get(id)||[])if(!children.includes(k))grandChildren.add(k);
  cols.set(-2,[...grandParents].sort((a,b)=>a-b));
  cols.set(2,[...grandChildren].sort((a,b)=>a-b));
  const coords=new Map();
  for(const [column,ids] of cols){
   ids.forEach((id,i)=>coords.set(id,{x:column*156,y:(i-(ids.length-1)/2)*39}));
  }
  return coords;
 }
 function drawProofGraph(){
  if(!proofCtx||pane!=="research")return;
  const rect=proofCanvas.getBoundingClientRect?.()||{width:340,height:220};
  const w=Math.max(200,Math.min(900,rect.width||340));
  const h=Math.max(150,Math.min(540,rect.height||220));
  const pixelRatio=Math.min(2,globalThis.devicePixelRatio||1);
  proofCanvas.width=Math.round(w*pixelRatio);
  proofCanvas.height=Math.round(h*pixelRatio);
  const c=proofCtx;c.setTransform(pixelRatio,0,0,pixelRatio,0,0);
  c.fillStyle="#101e27";c.fillRect(0,0,w,h);
  const overview=graphMode==="overview";
  const points=overview?proofCoordinates:localProofPositions();
  const fullW=(tech.summary.maxDepth+1)*210+60;
  const fullH=Math.max(...[...byDepth.values()].map(arr=>arr.length))*26+100;
  const baseScale=overview?Math.min((w-20)/fullW,(h-20)/fullH):
    Math.min(.85,Math.max(.6,(w-24)/470));
  const scale=baseScale*graphZoom;
  const center=proofById.get(selectedProof);
  const xyCenter=overview?{x:fullW/2,y:fullH/2}:{x:0,y:0};
  const at=(pos)=>({
   x:w/2+(pos.x-xyCenter.x)*scale+graphShift.x,
   y:h/2+(pos.y-xyCenter.y)*scale+graphShift.y
  });
  const highlight=new Set([selectedProof,...center.parents,...(proofChildren.get(selectedProof)||[])]);
  c.lineWidth=overview?.7:1.5;
  for(const node of tech.nodes){
   if(!points.has(node.id))continue;
   const to=at(points.get(node.id));
   for(const parent of node.parents){
    if(!points.has(parent))continue;
    const from=at(points.get(parent));
    const isLocal=highlight.has(node.id)&&highlight.has(parent);
    c.strokeStyle=isLocal?"#b2d1be":overview?"#4963727a":"#4e7485";
    c.lineWidth=isLocal&& !overview?2:overview?.6:1.1;
    c.beginPath();c.moveTo(from.x,from.y);c.lineTo(to.x,to.y);c.stroke();
   }
  }
  graphHitboxes=[];
  for(const node of tech.nodes){
   if(!points.has(node.id))continue;
   const pos=at(points.get(node.id)),research=proofStatusOf(node);
   const selectedNode=node.id===selectedProof;
   const r=overview?Math.max(1.35,scale*8):selectedNode?7:5;
   c.fillStyle=selectedNode?"#ffd99c":research==="studied"?"#7ed4c7":
     research==="ready"?"#bfd7a3":"#577484";
   c.beginPath();c.arc(pos.x,pos.y,r,0,Math.PI*2);c.fill();
   if(!overview&&(selectedNode||highlight.has(node.id))){
    c.font=selectedNode?"bold 12px system-ui":"10px system-ui";
    c.fillStyle=selectedNode?"#fae6ba":"#bdcfd2";
    c.fillText("#"+String(node.id+1).padStart(3,"0"),pos.x+8,pos.y-8);
   }
   graphHitboxes.push({id:node.id,x:pos.x,y:pos.y});
  }
  c.fillStyle="#a9c7cc";c.font="11px system-ui";
  c.fillText(overview?"全465件 / 629辺 — 検索から拡大":"証明の前提 ← 対象 → 後続の定理",8,15);
 }
 function renderProofDetails(){
  const n=proofById.get(selectedProof),d=$("proof-details");
  const parents=n.parents.map(id=>proofById.get(id)),children=(proofChildren.get(n.id)||[]).map(id=>proofById.get(id));
  const cost=F.proofCost(n),can=F.proofAvailable(world,n);
  const links=(arr,max)=>arr.slice(0,max).map(p=>'<button type="button" class="proof-link" data-proof-nav="'+p.id+'">'+
    esc(p.label)+'</button>').join("")+(arr.length>max?'<small>ほか '+(arr.length-max)+'件。検索で確認できます。</small>':"");
  d.innerHTML='<strong>'+esc(n.label)+'</strong><small>初期定理 #'+String(n.id+1).padStart(3,"0")+
    ' / '+esc(n.chapter)+' / 深さ '+n.depth+' / '+esc(proofStateLabel(n))+'</small>'+
    '<div style="margin-top:6px">直接の証明前提：'+parents.length+'件 ／ この定理を直接使う後続：'+children.length+'件</div>'+
    (parents.length?'<div class="proof-predecessors">'+links(parents,12)+'</div>':'<small>初期465定理に属する直接前提はありません。定義・外部補題などの依存は別に保持。</small>')+
    '<div style="margin-top:6px">後続の定理</div>'+
    (children.length?'<div class="proof-successors">'+links(children,8)+'</div>':'<small>初期集合内で直接の後続参照なし</small>')+
    '<button type="button" id="study-proof" '+(can?"":"disabled")+'>'+
      (hasProof(n)?"研究済":proofReady(n)?"研究 "+cost+"ポイント":"前提未解明")+'</button>'+
    '<details><summary>証明ソースと他の依存を確認</summary><small>'+
    esc(n.name)+' — '+esc(n.file)+':'+n.line+
    '</small><small>その他の初期宣言・補助定理への直接参照 '+n.otherProjectRefs.length+
    '件。この参照は定理ノード間の629本には含めていません。</small></details>';
  d.querySelectorAll("[data-proof-nav]").forEach(b=>b.addEventListener("click",()=>selectProof(Number(b.dataset.proofNav))));
  const btn=$("study-proof");
  if(btn)btn.addEventListener("click",()=>{
   if(F.researchProof(world,n)){
    persist();announce("研究完了："+n.label+"。後続の定理へ進めます。");
    renderTech();renderProof(true);drawProofGraph();refresh();
   }
  });
 }
 function renderProof(force=false){
  if(!world||pane!=="research")return;
  const done=world.proofs.length;
  $("proof-metrics").textContent=done+" / 465 解明 · 629直接証明辺 · 146基礎ノード";
  const q=proofSearch.trim().toLowerCase();
  const candidates=tech.nodes.filter(n=>{
   if(proofSchool!=="all"&&proofSchool!==n.school)return false;
   if(proofStatus!=="all"&&proofStatus!==proofStatusOf(n))return false;
   if(!q)return true;
   return (n.label+" "+n.chapter+" "+n.name+" "+"No."+String(n.id+1).padStart(3,"0")).toLowerCase().includes(q);
  }).sort((a,b)=>(a.depth-b.depth)||(a.id-b.id));
  $("proof-result-count").textContent=candidates.length+" / 465";
  const list=$("proof-results");
  const signature=done+"|"+world.science+"|"+q+"|"+proofStatus+"|"+proofSchool+"|"+selectedProof;
  if(!force&&list.dataset?.signature===signature){
   drawProofGraph();return;
  }
  if(list.dataset)list.dataset.signature=signature;
  list.innerHTML=candidates.slice(0,36).map(n=>'<button type="button" data-proof-result="'+n.id+
    '" aria-pressed="'+(selectedProof===n.id)+'" class="proof-result '+proofStatusOf(n)+'">'+
    '<span class="mono">#'+String(n.id+1).padStart(3,"0")+'</span><span>'+
    esc(n.label)+'<small>'+esc(n.chapter)+' · 深さ'+n.depth+
    ' · 親'+n.parents.length+'件</small></span><em>'+
    (hasProof(n)?"✓":proofReady(n)?F.proofCost(n)+" P":"鍵")+
    '</em></button>').join("")+
    (candidates.length>36?'<small style="padding:6px">最初の36件を表示中。検索や分野で絞り込んでください。</small>':"");
  list.querySelectorAll("[data-proof-result]").forEach(b=>b.addEventListener("click",()=>selectProof(Number(b.dataset.proofResult))));
  renderProofDetails();drawProofGraph();
 }
 function setupProof(){
  $("proof-search").addEventListener("input",e=>{
   proofSearch=e.target.value||"";renderProof(true);
  });
  $("proof-filter").addEventListener("change",e=>{
   proofStatus=e.target.value;renderProof(true);
  });
  $("proof-school").addEventListener("change",e=>{
   proofSchool=e.target.value;renderProof(true);
  });
  $("proof-overview").addEventListener("click",()=>{
   graphMode="overview";graphShift={x:0,y:0};graphZoom=1;drawProofGraph();
  });
  $("proof-center").addEventListener("click",()=>{
   graphMode="focus";graphShift={x:0,y:0};graphZoom=1;drawProofGraph();
  });
  if(proofCanvas){
   const distance=points=>Math.hypot(points[0].x-points[1].x,points[0].y-points[1].y);
   proofCanvas.addEventListener("pointerdown",e=>{
    proofPointerStop(e);
    const id=e.pointerId??"pointer";
    proofCanvas.setPointerCapture?.(e.pointerId);
    graphPointers.set(id,{x:e.clientX,y:e.clientY});
    if(graphPointers.size>=2){
     const pair=[...graphPointers.values()].slice(0,2);
     graphPinch={distance:Math.max(1,distance(pair)),zoom:graphZoom};
     graphPointer=null;return;
    }
    graphPointer={id,x:e.clientX,y:e.clientY,oldX:e.clientX,oldY:e.clientY,moved:false};
   });
   proofCanvas.addEventListener("pointermove",e=>{
    const id=e.pointerId??"pointer";
    if(graphPointers.has(id))graphPointers.set(id,{x:e.clientX,y:e.clientY});
    if(graphPointers.size>=2&&graphPinch){
     const pair=[...graphPointers.values()].slice(0,2);
     graphZoom=Math.max(.6,Math.min(9,graphPinch.zoom*distance(pair)/graphPinch.distance));
     drawProofGraph();return;
    }
    if(!graphPointer||graphPointer.id!==id)return;
    const dx=e.clientX-graphPointer.oldX,dy=e.clientY-graphPointer.oldY;
    if(Math.abs(e.clientX-graphPointer.x)+Math.abs(e.clientY-graphPointer.y)>8)graphPointer.moved=true;
    if(graphPointer.moved){graphShift.x+=dx;graphShift.y+=dy;drawProofGraph();}
    graphPointer.oldX=e.clientX;graphPointer.oldY=e.clientY;
   });
   proofCanvas.addEventListener("pointerup",e=>{
    const id=e.pointerId??"pointer";
    graphPointers.delete(id);
    if(graphPinch){
     if(graphPointers.size<2)graphPinch=null;
     graphPointer=null;return;
    }
    if(!graphPointer||graphPointer.id!==id)return;
    const moved=graphPointer.moved;graphPointer=null;
    if(moved)return;
    const box=proofCanvas.getBoundingClientRect?.()||{left:0,top:0,width:340,height:220};
    const x=e.clientX-box.left,y=e.clientY-box.top;
    let best=null,d=27; // Android fingertips, rather than a mouse-size 14px hitbox.
    for(const h of graphHitboxes){
     const dist=Math.hypot(x-h.x,y-h.y);
     if(dist<d){d=dist;best=h.id;}
    }
    if(best!==null)selectProof(best);
   });
   proofCanvas.addEventListener("pointercancel",()=>{
    graphPointers.clear();graphPointer=null;graphPinch=null;
   });
  }
 }
 function proofPointerStop(e){e.preventDefault?.();}
 function renderTech(){
  $("technologies").innerHTML=upgrades.nodes.map(t=>{
   const known=world.unlocks.includes(t.id);
   const missing=t.prerequisites.filter(p=>!world.unlocks.includes(p.id));
   const paper=t.gateProof?proofByName.get(t.gateProof):null;
   const mustStudy=paper&&!world.proofNames.includes(paper.name);
   const afford=F.techAvailable(world,t);
   const label=known?"開発済":missing.length?"設計の前提待ち":mustStudy?"証明が必要":"改良 "+t.cost+"点";
   const prereqs=t.prerequisites.map(p=>knownTech.get(p.id)?.label).filter(Boolean);
   return '<article class="technode '+(known?"known":afford?"available":"locked")+'">'+
    '<div class="tech-top"><strong>'+esc(t.label)+'</strong><small class="mono">'+
    (known?"✓":"COST "+t.cost)+'</small></div>'+
    '<p>'+esc(t.description)+'</p>'+
    (prereqs.length?'<div class="prereqs">工場の前提：'+esc(prereqs.join(" / "))+'</div>':"")+
    (paper?'<div class="prereqs">証明の前提：'+esc(paper.label)+
      (mustStudy?"（未研究）":"（解明済）")+
      '</div><button type="button" data-proof-jump="'+paper.id+'">依存の定理を見る</button>':"")+
    '<button data-unlock="'+esc(t.id)+'" type="button" '+(known||!afford?"disabled":"")+
    '>'+esc(label)+'</button></article>';
  }).join("");
  $("technologies").querySelectorAll("[data-proof-jump]").forEach(el=>el.addEventListener("click",()=>{
    selectProof(Number(el.dataset.proofJump));
  }));
  $("technologies").querySelectorAll("[data-unlock]").forEach(el=>el.addEventListener("click",()=>{
   const t=knownTech.get(el.dataset.unlock);
   if(F.unlock(world,t)){
    announce("工場改良完了："+t.label+"。実際の生産速度・設備が変化しました。");
    persist();refresh();
   }
  }));
 }
 const dossiers={
  doc3:["封筒 A / 回路の痕跡","最初の制御回路に接続記録が残っている。工程は単独では動かない。物流と熱処理の研究が開ける。"],
  doc10:["封筒 B / 東方の鉱脈","測量図の欠けた部分を補完した。東部地区に新しい鉄・銅鉱脈がある。新しい区画へ建設できる。"],
  doc25:["封筒 C / 量産の設計","小さな工程を繋ぐ規則が、大規模な循環路へと変わる。生産の飽和と詰まりを改めて調べよ。"]
 };
 function renderDocuments(){
  const docs=world.documents;
  $("documents").innerHTML=docs.length?docs.map((id,i)=>{
   const [title,desc]=dossiers[id]||[id,"未知の記録"];
   return '<article><div class="docno">FILE '+String(i+1).padStart(2,"0")+
    ' / RECOVERED</div><h3>'+esc(title)+'</h3><p>'+esc(desc)+'</p></article>';
  }).join(""):'<p>まだ文書がありません。研究所で回路を3個処理すると、最初の設計書が見つかります。</p>';
 }
 function refresh(){
  if(!world)return;
  $("science-total").textContent=world.totalScience+" / 30";
  $("science-bar").style.width=Math.min(100,world.totalScience/30*100)+"%";
  $("science-stock").textContent=world.science;
  $("power").textContent=Math.round(world.energy)+" / "+world.energyMax;
  $("transported").textContent=world.transported;
  $("play").textContent=world.status==="paused"?"▶ 再開":"II 停止";
  $("speed").textContent="速度 ×"+speed;
  $("log").innerHTML=world.notes.slice(0,5).map(x=>"<div>"+esc(x)+"</div>").join("");
  if(F.pendingRepairs(world).length){$("status").textContent="切断された搬送路が"+F.pendingRepairs(world).length+"か所。黄色の欠損セルをタップして修理してください。";}
  else if(world.challenge&&world.totalScience===0)$("status").textContent="搬送路が復旧しました。制御回路が組立機から研究所へ流れるのを確認しよう。";
  if(world.status==="complete")$("status").textContent="目標達成。自動化は続けられます。次はより短時間で量産しよう。";
  renderPalette();if(pane==="research"){renderTech();renderProof();}renderDocuments();renderInspector();draw();
 }
 function select(x,y){selected={x,y};showPane("inspect");renderInspector();draw();}
 function interact(x,y,direction=dir){
  if(!F.inside(x,y))return;
  if(tool==="pan"){
   if(F.repairBlueprint(world,x,y)){
    selected={x,y};persist();refresh();
    announce(F.pendingRepairs(world).length?"補修成功！ もう一つの黄色い断線を復旧しよう。":"接続完了。自動生産が始まります。");
   }else select(x,y);
   return;
  }
  if(!F.isDiscovered(world,x,y)){announce("この地区はまだ未解読です。設計書を回収するか測量技術を研究しよう。");return;}
  const okay=F.place(world,x,y,tool,direction);
  if(!okay){announce("そこには配置できません。採掘機は鉱脈、発電機は石炭鉱脈上に設置してください。");return;}
  selected={x,y};persist();renderInspector();draw();
 }
 function drawBeltPath(prev,next){
  if(!prev||!next)return;
  let x=prev.x,y=prev.y;const sx=next.x,sy=next.y;
  while(x!==sx||y!==sy){
   const dx=sx===x?0:Math.sign(sx-x),dy=dx?0:Math.sign(sy-y);
   const direction=F.DX.findIndex((n,i)=>n===dx&&F.DY[i]===dy);
   if(direction<0)break;
   const t=world.tiles[F.idx(x,y)];
   if(t.building?.kind==="belt")t.building.dir=direction;
   else if(!t.building)F.place(world,x,y,"belt",direction);
   x+=dx;y+=dy;
   if(F.inside(x,y)&&F.isDiscovered(world,x,y)&&!world.tiles[F.idx(x,y)].building)
    F.place(world,x,y,"belt",direction);
   if(!F.inside(x,y))break;
  }
 }
 function xyOfEvent(e){
  const r=canvas.getBoundingClientRect();
  return {x:e.clientX-r.left,y:e.clientY-r.top};
 }
 canvas.addEventListener("pointerdown",e=>{
  if(e.button!==undefined&&e.button!==0)return;
  e.preventDefault();canvas.setPointerCapture?.(e.pointerId);
  const id=e.pointerId??"pointer";
  const p=xyOfEvent(e);
  mapPointers.set(id,p);
  if(mapPointers.size>=2){
   const pair=[...mapPointers.values()].slice(0,2);
   const mid={x:(pair[0].x+pair[1].x)/2,y:(pair[0].y+pair[1].y)/2};
   const unit=tileSize();
   mapPinch={distance:Math.max(1,Math.hypot(pair[0].x-pair[1].x,pair[0].y-pair[1].y)),
    startZoom:zoom,anchorX:camX+(mid.x-layoutW/2)/unit,anchorY:camY+(mid.y-layoutH/2)/unit};
   touch=null;return;
  }
  const w=screenToWorld(p.x,p.y);
  touch={pointerId:id,x:p.x,y:p.y,oldX:p.x,oldY:p.y,original:w,last:w,moved:false,mode:tool};
  if(tool==="belt"&&w)interact(w.x,w.y,dir);
 });
 canvas.addEventListener("pointermove",e=>{
  const id=e.pointerId??"pointer",p=xyOfEvent(e);
  if(mapPointers.has(id))mapPointers.set(id,p);
  if(mapPinch&&mapPointers.size>=2){
   e.preventDefault();
   const pair=[...mapPointers.values()].slice(0,2);
   const dist=Math.max(1,Math.hypot(pair[0].x-pair[1].x,pair[0].y-pair[1].y));
   const mid={x:(pair[0].x+pair[1].x)/2,y:(pair[0].y+pair[1].y)/2};
   zoom=Math.max(.5,Math.min(3.2,mapPinch.startZoom*dist/mapPinch.distance));
   const unit=tileSize();
   camX=mapPinch.anchorX-(mid.x-layoutW/2)/unit;
   camY=mapPinch.anchorY-(mid.y-layoutH/2)/unit;
   camX=Math.max(-1,Math.min(F.W+1,camX));
   camY=Math.max(-1,Math.min(F.H+1,camY));
   draw();return;
  }
  if(!touch||touch.pointerId!==id)return;
  e.preventDefault();
  const dx=p.x-touch.oldX,dy=p.y-touch.oldY;
  if(Math.abs(p.x-touch.x)+Math.abs(p.y-touch.y)>8)touch.moved=true;
  if(touch.mode==="belt"){
   const w=screenToWorld(p.x,p.y);
   if(w&&touch.last&&(w.x!==touch.last.x||w.y!==touch.last.y)){
    drawBeltPath(touch.last,w);touch.last=w;selected=w;draw();
   }
  }else if(touch.mode==="pan"||touch.moved){
   camX-=dx/tileSize();camY-=dy/tileSize();
   camX=Math.max(-1,Math.min(F.W+1,camX));camY=Math.max(-1,Math.min(F.H+1,camY));draw();
  }
  touch.oldX=p.x;touch.oldY=p.y;
 });
 function endTouch(e){
  const id=e.pointerId??(touch?.pointerId??"pointer");
  mapPointers.delete(id);
  if(mapPinch){
   if(mapPointers.size<2)mapPinch=null;
   touch=null;return;
  }
  if(!touch||touch.pointerId!==id)return;
  const mode=touch.mode,moved=touch.moved,initial=touch.original;
  if(mode==="belt"){persist();renderInspector();}
  else if(!moved&&initial)interact(initial.x,initial.y);
  touch=null;
 }
 canvas.addEventListener("pointerup",endTouch);
 canvas.addEventListener("pointercancel",()=>{touch=null;mapPointers.clear();mapPinch=null;persist();});
 viewport.addEventListener("wheel",e=>{
  e.preventDefault();zoom=Math.max(.5,Math.min(3.2,zoom*(e.deltaY<0?1.12:.89)));draw();
 },{passive:false});
 function hook(){
  document.querySelectorAll("[data-category]").forEach(el=>el.addEventListener("click",()=>{
   category=el.dataset.category;renderPalette();
  }));
  document.querySelectorAll("[data-panel]").forEach(el=>el.addEventListener("click",()=>showPane(el.dataset.panel)));
  document.querySelectorAll("[data-mobile-screen]").forEach(el=>
    el.addEventListener("click",()=>setMobileScreen(el.dataset.mobileScreen)));
  $("research-shortcut").addEventListener("click",()=>{
   setMobileScreen("research");
   if(typeof window!=="undefined"&&window.innerWidth>950)
     $("view-research").scrollIntoView?.({behavior:"smooth",block:"center"});
  });
  $("proof-back").addEventListener("click",()=>setMobileScreen("factory"));
  $("rotate-tool").addEventListener("click",()=>{dir=(dir+1)%4;renderPalette();});
  $("zoom-in").addEventListener("click",()=>{zoom=Math.min(3.2,zoom*1.22);draw();});
  $("zoom-out").addEventListener("click",()=>{zoom=Math.max(.5,zoom/1.22);draw();});
  $("rotate-selected").addEventListener("click",()=>{
   if(selected&&F.rotate(world,selected.x,selected.y)){persist();refresh();}
  });
  $("delete-selected").addEventListener("click",()=>{
   if(selected&&F.removeMachine(world,selected.x,selected.y)){persist();refresh();}
  });
  $("play").addEventListener("click",()=>{
   world.status=world.status==="paused"?"playing":"paused";persist();refresh();
  });
  $("speed").addEventListener("click",()=>{speed=speed===1?4:speed===4?12:1;refresh();});
  $("demo").addEventListener("click",()=>{
   if(world.totalScience>0 && !globalThis.confirm("工場と今までの生産成果をリセットして、試運転ラインを再配置しますか？"))return;
   F.demoBlueprint(world);world.status="playing";persist();refresh();
   announce("完成ラインを再配置しました。流れる部品を見て、詰まりを改善しましょう。");
  });
  $("new-world").addEventListener("click",()=>{
   if(!globalThis.confirm("工場と研究をすべてやり直しますか？"))return;
   world=F.newWorld(Date.now()>>>0);world.status="playing";persist();refresh();
   announce("新しい空の工場地区。採掘機と発電機から組み立ててください。");
  });
  $("clear-buildings").addEventListener("click",()=>{
   if(!globalThis.confirm("すべての建物を撤去しますか？"))return;
   for(const t of world.tiles)t.building=null;
   persist();refresh();announce("建物を撤去しました。資源は残っています。");
  });
  $("help").addEventListener("click",()=>{
   helpOpen=!helpOpen;
   announce(helpOpen?
    "まず試運転ラインの部品を観察しよう。左下のベルトを選ぶとドラッグ敷設。研究所に回路が届くと技術を解放できます。見えない東部は設計書で開きます。":
    F.tip(world));
  });
  document.addEventListener("keydown",e=>{
   if(e.target?.tagName==="INPUT"||e.ctrlKey||e.metaKey||e.altKey)return;
   const key=e.key.toLowerCase();
   if(key==="r"){dir=(dir+1)%4;renderPalette();}
   if(key==="escape")setTool("pan");
   if(key===" "){e.preventDefault();world.status=world.status==="paused"?"playing":"paused";refresh();}
  });
 }
 function start(){
  setupProof();hook();setTool("pan");
  if(deepLinkView==="research"){
   setMobileScreen("research",true);
   document.body?.classList?.add("research-direct");
   showPane("research");
  }else setMobileScreen(mobileScreens.includes(deepLinkView)?deepLinkView:"factory");
  resize();refresh();
  const ro=typeof ResizeObserver!=="undefined"?new ResizeObserver(resize):null;
  if(ro)ro.observe(viewport);else window.addEventListener("resize",resize);
  clock=setInterval(()=>{
   if(world.status==="playing"||world.status==="complete"){
    F.advance(world,speed);
    if(world.tick-lastSave>24){lastSave=world.tick;persist();}
   }
   // Draw every interval to keep animation responsive even while paused.
   $("science-total").textContent=world.totalScience+" / 30";
   $("science-bar").style.width=Math.min(100,world.totalScience/30*100)+"%";
   $("science-stock").textContent=world.science;
   $("power").textContent=Math.round(world.energy)+" / "+world.energyMax;
   $("transported").textContent=world.transported;
   if(world.tick%6===0){if(pane==="research"){renderTech();renderProof();}renderDocuments();renderInspector();
    $("log").innerHTML=world.notes.slice(0,5).map(x=>"<div>"+esc(x)+"</div>").join("");}
   draw();
  },110);
 }
 start();
})();
