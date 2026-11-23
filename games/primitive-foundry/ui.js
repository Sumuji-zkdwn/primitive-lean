"use strict";
(async function(){
 const F=globalThis.PrimitiveFoundry;
 if(!F)throw Error("Factory engine not found");
 const $=id=>document.getElementById(id);
 const esc=s=>String(s).replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
 const techSource=$("factory-tech")?.textContent;
 const tech=techSource?JSON.parse(techSource):await (await fetch("./tech.json")).json();
 const knownTech=new Map(tech.nodes.map(t=>[t.id,t]));
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
 if(!ctx){$("status").textContent="Canvas描画を利用できません。";return;}
 const STORAGE="primitive-foundry-save-v1";
 let world=null,category="logistics",tool="pan",dir=0,zoom=1;
 let pane="inspect",selected=null,clock=null,speed=1,touch=null,lastSave=0,helpOpen=false;
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
 world=load()||F.demoBlueprint(F.newWorld(20261124));
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
  $("tip").textContent=next==="pan"?"建物をタップして調査。ドラッグで地図を動かします。":
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
 function showPane(id){
  pane=id;
  for(const x of ["inspect","research","documents"])$("view-"+x).classList.toggle("active",x===id);
  document.querySelectorAll("[data-panel]").forEach(el=>
    el.setAttribute("aria-selected",String(el.dataset.panel===id)));
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
 function renderTech(){
  $("technologies").innerHTML=tech.nodes.map(t=>{
   const known=world.unlocks.includes(t.id);
   const missing=t.prerequisites.filter(p=>!world.unlocks.includes(p.id));
   const afford=F.techAvailable(world,t);
   const label=known?"獲得済":missing.length?"要前提":"研究 "+t.cost+"点";
   const prereqs=t.prerequisites.map(p=>knownTech.get(p.id)?.label).filter(Boolean);
   const detail=t.prerequisites.reduce((n,p)=>n+p.proofReferences,0);
   return '<article class="technode '+(known?"known":afford?"available":"locked")+'">'+
    '<div class="tech-top"><strong>'+esc(t.label)+'</strong><small class="mono">'+
    (known?"✓":"COST "+t.cost)+'</small></div>'+
    '<p>'+esc(t.description)+'</p>'+
    (prereqs.length?'<div class="prereqs">前提：'+esc(prereqs.join(" / "))+'</div>':"")+
    '<button data-unlock="'+esc(t.id)+'" type="button" '+(known||!afford?"disabled":"")+'>'+esc(label)+'</button>'+
    '<details><summary>数学的な出典（証明参照 '+detail+'件）</summary><div>'+esc(t.path)+
    '</div><small>ファイル単位の参照で、定理間の完全なDAGではありません。</small></details></article>';
  }).join("");
  $("technologies").querySelectorAll("[data-unlock]").forEach(el=>el.addEventListener("click",()=>{
   const t=knownTech.get(el.dataset.unlock);
   if(F.unlock(world,t)){
    announce("研究成功："+t.label+"。生産ラインの新機能が有効になりました。");
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
  if(world.status==="complete")$("status").textContent="目標達成。自動化は続けられます。次はより短時間で量産しよう。";
  renderPalette();renderTech();renderDocuments();renderInspector();draw();
 }
 function select(x,y){selected={x,y};showPane("inspect");renderInspector();draw();}
 function interact(x,y,direction=dir){
  if(!F.inside(x,y))return;
  if(tool==="pan"){select(x,y);return;}
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
  const p=xyOfEvent(e),w=screenToWorld(p.x,p.y);
  touch={x:p.x,y:p.y,oldX:p.x,oldY:p.y,original:w,last:w,moved:false,mode:tool};
  if(tool==="belt"&&w)interact(w.x,w.y,dir);
 });
 canvas.addEventListener("pointermove",e=>{
  if(!touch)return;e.preventDefault();
  const p=xyOfEvent(e),dx=p.x-touch.oldX,dy=p.y-touch.oldY;
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
  if(!touch)return;
  const mode=touch.mode,moved=touch.moved,initial=touch.original;
  if(mode==="belt"){persist();renderInspector();}
  else if(!moved&&initial)interact(initial.x,initial.y);
  touch=null;
 }
 canvas.addEventListener("pointerup",endTouch);
 canvas.addEventListener("pointercancel",()=>{touch=null;persist();});
 viewport.addEventListener("wheel",e=>{
  e.preventDefault();zoom=Math.max(.5,Math.min(3.2,zoom*(e.deltaY<0?1.12:.89)));draw();
 },{passive:false});
 function hook(){
  document.querySelectorAll("[data-category]").forEach(el=>el.addEventListener("click",()=>{
   category=el.dataset.category;renderPalette();
  }));
  document.querySelectorAll("[data-panel]").forEach(el=>el.addEventListener("click",()=>showPane(el.dataset.panel)));
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
  hook();setTool("pan");resize();refresh();
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
   if(world.tick%6===0){renderTech();renderDocuments();renderInspector();
    $("log").innerHTML=world.notes.slice(0,5).map(x=>"<div>"+esc(x)+"</div>").join("");}
   draw();
  },110);
 }
 start();
})();
