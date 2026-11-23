"use strict";
/*
 PRIMITIVE FOUNDRY: original deterministic factory simulation.
 Mechanics: tile belts, backpressure, mining, processing, power, research.
 Proof-derived TECH PREREQUISITES are in tech.json, a selected real file-level
 proof-reference DAG. Upgrade effects are GAME DESIGN, not Lean theorems.
 */
(function(root,factory){
 const game=factory();
 if(typeof module==="object"&&module.exports)module.exports=game;
 root.PrimitiveFoundry=game;
})(globalThis,function(){
 const W=24,H=18,SIZE=W*H;
 const DX=[1,0,-1,0],DY=[0,1,0,-1],DIR_SYM=["→","↓","←","↑"];
 const ITEMS={
  ironOre:{label:"鉄鉱石",color:"#9ab6cd"},
  copperOre:{label:"銅鉱石",color:"#d99b63"},
  ironPlate:{label:"鉄板",color:"#c8d6e1"},
  copperPlate:{label:"銅板",color:"#f6b06c"},
  gear:{label:"歯車",color:"#c4c5bd"},
  wire:{label:"導線",color:"#f1d47a"},
  circuit:{label:"制御回路",color:"#81e1b4"}
 };
 const MACHINES={
  belt:{label:"ベルト",hint:"資源を一方向に流す",period:2},
  miner:{label:"採掘機",hint:"鉱脈上に配置。前方へ原鉱を出す",period:5,power:1},
  ironFurnace:{label:"鉄の精錬炉",hint:"鉄鉱石1 → 鉄板1",period:5,power:1,
    inputs:{ironOre:1},output:{ironPlate:1}},
  copperFurnace:{label:"銅の精錬炉",hint:"銅鉱石1 → 銅板1",period:5,power:1,
    inputs:{copperOre:1},output:{copperPlate:1}},
  press:{label:"プレス機",hint:"鉄板2 → 歯車1",period:6,power:1,
    inputs:{ironPlate:2},output:{gear:1}},
  winder:{label:"巻線機",hint:"銅板1 → 導線2",period:5,power:1,
    inputs:{copperPlate:1},output:{wire:2}},
  assembler:{label:"組立機",hint:"歯車1 + 導線2 → 回路1",period:9,power:2,
    inputs:{gear:1,wire:2},output:{circuit:1}},
  lab:{label:"研究所",hint:"回路1 → 研究ポイント1",period:7,power:2,inputs:{circuit:1}},
  generator:{label:"発電機",hint:"石炭鉱脈に置いて給電",period:9,power:0},
  junction:{label:"分配器",hint:"受け取った部品を前方・右方へ交互に出す",period:1}
 };
 const BUILDABLE=Object.keys(MACHINES);
 const DIRS=DX.map((dx,i)=>({dx,dy:DY[i]}));
 const idx=(x,y)=>y*W+x;
 const xy=i=>[i%W,Math.floor(i/W)];
 const inside=(x,y)=>Number.isInteger(x)&&Number.isInteger(y)&&x>=0&&x<W&&y>=0&&y<H;
 const near=(i,dir)=>{
  const [x,y]=xy(i); const X=x+DX[dir],Y=y+DY[dir];
  return inside(X,Y)?idx(X,Y):-1;
 };
 const clone=x=>JSON.parse(JSON.stringify(x));
 function makeTile(x,y){
  const sample=(x*13+y*23+(x*y*7))%43;
  const water=(x>20&&y>13)||(x<2&&y<3)||((x===20||x===21)&&y===15);
  return {ground:water?"water":"floor",tone:sample,ore:null,qty:0,building:null};
 }
 function orePatch(world,cx,cy,type,amount=160){
  for(const [dx,dy,scale] of [[0,0,1],[1,0,.72],[-1,0,.62],[0,1,.74],[0,-1,.67],[1,1,.54],[-1,-1,.45]]){
   const x=cx+dx,y=cy+dy;
   if(!inside(x,y))continue;
   const cell=world.tiles[idx(x,y)];
   if(cell.ground!=="water"){cell.ore=type;cell.qty=Math.round(amount*scale);}
  }
 }
 function newMachine(kind,dir=0){
  if(!MACHINES[kind])throw Error("unknown machine "+kind);
  return {kind,dir:((dir%4)+4)%4,item:null,queue:[],stock:{},
    progress:0,active:false,processed:0,alternate:0,blocked:false};
 }
 function newWorld(seed=1){
  const tiles=[];
  for(let y=0;y<H;y++)for(let x=0;x<W;x++)tiles.push(makeTile(x,y));
  const w={schema:1,seed,tiles,tick:0,energy:180,energyMax:800,
   science:0,totalScience:0,seen:0,documents:[],history:[],
   unlocks:["geometry","variation","design","calculus"],proofs:[],proofNames:[],
   selected:null,generated:{},status:"playing",built:0,transported:0,
   products:{},notes:["鉄鉱石 → 鉄板 → 歯車、銅鉱石 → 銅板 → 導線。組立機で制御回路を作り、研究所へ送ろう。"]};
  orePatch(w,3,5,"ironOre",240);
  orePatch(w,3,11,"copperOre",210);
  orePatch(w,3,15,"coal",260);
  orePatch(w,18,4,"ironOre",170);
  orePatch(w,19,11,"copperOre",170);
  orePatch(w,14,14,"coal",200);
  return w;
 }
 function record(w,text){
  if(w.notes[0]!==text)w.notes.unshift(text);
  if(w.notes.length>12)w.notes.length=12;
 }
 function setMachine(w,x,y,kind,dir=0,force=false){
  if(!inside(x,y)||!MACHINES[kind])return false;
  const cell=w.tiles[idx(x,y)];
  if(cell.ground==="water")return false;
  if(!force&&cell.building)return false;
  if(kind==="miner"&&(!cell.ore||cell.ore==="coal"||cell.qty<=0))return false;
  if(kind==="generator"&&(cell.ore!=="coal"||cell.qty<=0))return false;
  if(kind==="junction"&&!w.unlocks.includes("composition"))return false;
  cell.building=newMachine(kind,dir);w.built++;return true;
 }
 function removeMachine(w,x,y){
  if(!inside(x,y))return false;
  const tile=w.tiles[idx(x,y)];if(!tile.building)return false;
  tile.building=null;return true;
 }
 function rotate(w,x,y){
  if(!inside(x,y)||!w.tiles[idx(x,y)].building)return false;
  w.tiles[idx(x,y)].building.dir=(w.tiles[idx(x,y)].building.dir+1)%4;return true;
 }
 // The eastern ore field is found through a recovered document or a scanner.
 function isDiscovered(w,x,y){
  return x<=16||w.documents.includes("doc10")||w.unlocks.includes("reconstruction");
 }
 // Zero-cost construction is a deliberate sandbox accessibility choice.
 function place(w,x,y,kind,dir=0){
  if(w.status!=="playing"&&w.status!=="complete")return false;
  if(!inside(x,y)||!isDiscovered(w,x,y))return false;
  if(kind==="erase")return removeMachine(w,x,y);
  if(kind==="rotate")return rotate(w,x,y);
  return setMachine(w,x,y,kind,dir);
 }
 function supplyNeeds(m,item){
  const recipe=MACHINES[m.kind];
  if(m.kind==="junction")return m.queue.length<2;
  if(!recipe?.inputs?.[item])return false;
  const already=m.stock[item]||0;
  return already<recipe.inputs[item]*3;
 }
 function inject(w,dest,item){
  if(dest<0)return false;
  const tile=w.tiles[dest],m=tile.building;
  if(!m)return false;
  if(m.kind==="belt"){
   if(m.item!==null)return false;
   m.item=item;return true;
  }
  if(m.kind==="junction"){
   if(m.queue.length>=2)return false;
   m.queue.push(item);return true;
  }
  if(!supplyNeeds(m,item))return false;
  m.stock[item]=(m.stock[item]||0)+1;return true;
 }
 function recipeTime(w,kind){
  const base=MACHINES[kind]?.period||1;
  if((kind==="ironFurnace"||kind==="copperFurnace")&&w.unlocks.includes("gradient"))
   return Math.ceil(base/2);
  if(kind==="assembler"&&w.unlocks.includes("globalConsequences"))
   return Math.ceil(base/2);
  return base;
 }
 function outputItems(recipe){
  const out=[];
  if(recipe?.output)for(const [item,num] of Object.entries(recipe.output))
   for(let i=0;i<num;i++)out.push(item);
  return out;
 }
 function flushMachine(w,i){
  const m=w.tiles[i].building;
  if(!m||m.queue.length===0)return;
  if(m.kind==="belt")return;
  const target=near(i,m.dir);
  if(m.kind==="junction"){
   const first=(m.dir+(m.alternate===0?0:1))%4;
   const other=(m.dir+(m.alternate===0?1:0))%4;
   // If the first lane is blocked, try the other; do not destroy anything.
   for(const d of [first,other])if(inject(w,near(i,d),m.queue[0])){
    m.queue.shift();m.alternate^=1;m.blocked=false;return;
   }
   m.blocked=true;return;
  }
  if(inject(w,target,m.queue[0])){
   m.queue.shift();m.blocked=false;
  }else m.blocked=true;
 }
 // Belt step has snapshot capacity: one item per tile, no double movement in a tick.
 function moveBelts(w){
  if(!w.unlocks.includes("scaling")&&w.tick%2!==0)return;
  const moves=[],planned=new Set();
  for(let i=0;i<w.tiles.length;i++){
   const b=w.tiles[i].building;
   if(!b||b.kind!=="belt"||b.item===null)continue;
   const target=near(i,b.dir);
   if(target<0||planned.has(target))continue;
   const t=w.tiles[target].building;
   if(!t)continue;
   if(t.kind==="belt"&&t.item!==null)continue;
   if(t.kind==="junction"&&t.queue.length>=2)continue;
   if(t.kind!=="belt"&&t.kind!=="junction"&&!supplyNeeds(t,b.item))continue;
   planned.add(target);moves.push([i,target,b.item]);
  }
  for(const [src,dest,item] of moves){
   const b=w.tiles[src].building;
   if(!b||b.item!==item)continue;
   if(inject(w,dest,item)){b.item=null;w.transported++;}
  }
 }
 function canStart(m,inputs){
  if(!inputs)return false;
  return Object.entries(inputs).every(([item,count])=>(m.stock[item]||0)>=count);
 }
 function spendInputs(m,inputs){
  for(const [item,count] of Object.entries(inputs))m.stock[item]-=count;
 }
 function completeCycle(w,m,kind){
  if(kind==="lab"){
   w.science++;w.totalScience++;w.products.science=(w.products.science||0)+1;
   if([3,10,25].includes(w.totalScience)){
    const id="doc"+w.totalScience;
    if(!w.documents.includes(id)){
     w.documents.push(id);
     record(w,"古い設計書を発見：第"+w.documents.length+"断片。新しい研究分岐が読める。");
    }
   }
   if(w.totalScience>=30&&w.status!=="complete"){
    w.status="complete";
    record(w,"初期目標達成！ 30研究ポイントの生産ラインが動いた。構築は続けられる。");
   }
  }else{
   for(const item of outputItems(MACHINES[kind]))m.queue.push(item);
   for(const [item,num] of Object.entries(MACHINES[kind].output||{}))
    w.products[item]=(w.products[item]||0)+num;
  }
  m.processed++;
 }
 function stepOnce(w){
  if(w.status==="paused")return w;
  w.tick++;
  // Coal vein generators burn fuel without belts, letting the player solve
  // logistics first. Accumulated global power is constrained, never negative.
  for(let i=0;i<w.tiles.length;i++){
   const t=w.tiles[i],m=t.building;
   if(!m||m.kind!=="generator"||t.ore!=="coal"||t.qty<=0)continue;
   if(w.tick%MACHINES.generator.period===0&&w.energy<w.energyMax-60){
    t.qty--;
    w.energy=Math.min(w.energyMax,w.energy+
      (w.unlocks.includes("gradientBound")?180:90));
    w.products.burnedCoal=(w.products.burnedCoal||0)+1;
    m.active=true;m.processed++;
   }else m.active=false;
  }
  // Emit buffered results first, then advance packages in a two-phase belt step.
  for(let i=0;i<w.tiles.length;i++)flushMachine(w,i);
  moveBelts(w);
  for(let i=0;i<w.tiles.length;i++){
   const tile=w.tiles[i],m=tile.building;if(!m)continue;
   if(m.kind==="miner"){
    m.active=false;
    if(m.queue.length>0||!tile.ore||tile.qty<=0){m.blocked=m.queue.length>0;continue;}
    if(w.energy<1)continue;
    w.energy--;m.active=true;m.progress++;
    if(m.progress>=MACHINES.miner.period){
     m.progress=0;tile.qty--;m.queue.push(tile.ore);m.processed++;
     w.products[tile.ore]=(w.products[tile.ore]||0)+1;
    }
    continue;
   }
   const rule=MACHINES[m.kind];
   if(!rule.inputs)continue;
   // Stock can fill before a machine finishes, but only a finished output
   // buffer can block the next cycle.
   if(m.progress===0){
    if(m.queue.length>0||!canStart(m,rule.inputs)){m.active=false;continue;}
    spendInputs(m,rule.inputs);m.progress=1;
   }
   if(w.energy<rule.power){m.active=false;continue;}
   w.energy-=rule.power;m.active=true;
   if(m.progress>=recipeTime(w,m.kind)){
    m.progress=0;completeCycle(w,m,m.kind);
   }else m.progress++;
  }
  return w;
 }
 function advance(w,steps=1){
  for(let i=0;i<Math.min(steps,100000);i++)stepOnce(w);
  return w;
 }
 // Place a functioning demonstrator, then let the user tear down and optimize.
 function demoBlueprint(w){
  w.challenge=false;
  for(const t of w.tiles)t.building=null;
  w.tick=0;w.energy=260;w.science=0;w.totalScience=0;w.status="playing";
  w.products={};w.documents=[];w.transported=0;w.built=0;
  const put=(x,y,kind,dir)=>setMachine(w,x,y,kind,dir,true);
  put(3,15,"generator",0);
  put(3,5,"miner",0);put(4,5,"ironFurnace",0);
  for(const x of [5,6,7])put(x,5,"belt",0);
  put(8,5,"press",0);
  put(9,5,"belt",0);put(10,5,"belt",0);
  put(11,5,"belt",1);put(11,6,"belt",1);
  put(3,11,"miner",0);put(4,11,"copperFurnace",0);
  for(const x of [5,6,7])put(x,11,"belt",0);
  put(8,11,"winder",0);put(9,11,"belt",0);
  put(10,11,"belt",3);for(const y of [10,9,8])put(10,y,"belt",3);
  put(10,7,"belt",0);put(11,7,"assembler",0);
  put(12,7,"belt",0);put(13,7,"belt",0);
  put(14,7,"lab",0);
  record(w,"動く実験ラインを配置した。搬送が詰まる場所を探し、複製・改造して生産量を伸ばそう。");
  return w;
 }
 const REPAIRS=[
  {x:11,y:6,dir:1,description:"歯車ラインの南向きベルト"},
  {x:10,y:8,dir:3,description:"導線ラインの北向きベルト"}
 ];
 function pendingRepairs(w){
  if(!w.challenge)return [];
  return REPAIRS.filter(p=>{
   const m=w.tiles[idx(p.x,p.y)].building;
   return !m||m.kind!=="belt"||m.dir!==p.dir;
  });
 }
 function repairBlueprint(w,x,y){
  const hint=pendingRepairs(w).find(p=>p.x===x&&p.y===y);
  if(!hint)return false;
  const cell=w.tiles[idx(x,y)];
  if(cell.building?.kind==="belt")cell.building.dir=hint.dir;
  else if(!cell.building)setMachine(w,x,y,"belt",hint.dir,true);
  else return false;
  const remain=pendingRepairs(w).length;
  record(w,remain?hint.description+"を補修。残り"+remain+"か所。":
   "搬送路の復旧完了。研究所に材料が届きはじめる。");
  return true;
 }
 function challengeBlueprint(w){
  demoBlueprint(w);
  w.challenge=true;
  removeMachine(w,11,6);
  removeMachine(w,10,8);
  record(w,"工場に2か所の搬送路の切断がある。黄色の欠損セルをタップして復旧しよう。");
  return w;
 }
 function proofCost(node){
  return 1+Math.min(2,Math.floor(node.depth/5));
 }
 function proofAvailable(w,node){
  if(!node||!Number.isInteger(node.id)||!Array.isArray(node.parents))return false;
  if(!Array.isArray(w.proofs))w.proofs=[];
  return !w.proofs.includes(node.id)&&node.parents.every(id=>w.proofs.includes(id))&&
    w.science>=proofCost(node);
 }
 function researchProof(w,node){
  if(!proofAvailable(w,node))return false;
  w.science-=proofCost(node);w.proofs.push(node.id);
  if(!Array.isArray(w.proofNames))w.proofNames=[];
  w.proofNames.push(node.name);
  record(w,"証明の断片を復元："+node.label+"。次の依存先が開いた。");
  return true;
 }
 function techAvailable(w,tech){
  return !!tech&&!w.unlocks.includes(tech.id)&&
    (!tech.gateProof||(Array.isArray(w.proofNames)&&w.proofNames.includes(tech.gateProof)))&&
    tech.prerequisites.every(p=>w.unlocks.includes(p.id))&&w.science>=tech.cost;
 }
 function unlock(w,tech){
  if(!techAvailable(w,tech))return false;
  w.science-=tech.cost;w.unlocks.push(tech.id);
  record(w,"研究成功：「"+tech.label+"」。工場の能力が変化した。");
  return true;
 }
 function machineStatus(w,x,y){
  if(!inside(x,y))return null;
  const t=w.tiles[idx(x,y)],m=t.building;
  if(!m)return {ground:t.ground,ore:t.ore,qty:t.qty};
  const n=MACHINES[m.kind];
  return {kind:m.kind,label:n.label,dir:m.dir,stock:clone(m.stock),
   output:m.queue.slice(),item:m.item,progress:m.progress,processed:m.processed,
   blocked:m.blocked,active:m.active,ore:t.ore,qty:t.qty,
   hint:n.hint,cycle:recipeTime(w,m.kind)};
 }
 function counts(w){
  const out={};for(const tile of w.tiles){
   const type=tile.building?.kind;
   if(type)out[type]=(out[type]||0)+1;
  }return out;
 }
 function tip(w){
  const kinds=counts(w);
  if(!kinds.generator)return "発電機を石炭鉱脈に置こう。稼働には電気が必要だ。";
  if(!kinds.miner)return "採掘機を鉱脈に置き、矢印の先へベルトをつなごう。";
  if(!kinds.lab)return "生産した制御回路を研究所へ届けよう。";
  if(w.energy<10)return "電気が足りない。発電機の下の石炭が枯れていないか確認。";
  if(!w.totalScience)return "機械の出力方向、入力の品目、ベルトの曲がり角を点検しよう。";
  return "流れが詰まるところを観察し、採掘・製錬・組立の台数を増やそう。";
 }
 return Object.freeze({W,H,SIZE,DX,DY,DIR_SYM,ITEMS,MACHINES,BUILDABLE,
  idx,xy,near,inside,isDiscovered,newWorld,clone,setMachine,removeMachine,rotate,place,
  pendingRepairs,repairBlueprint,challengeBlueprint,
  inject,stepOnce,advance,demoBlueprint,proofCost,proofAvailable,researchProof,techAvailable,unlock,machineStatus,counts,tip});
});
