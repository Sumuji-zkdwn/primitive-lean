"use strict";
/* PRIMITIVE / ROGUE 465 — original 465 theorem catalog + 3 later world laws.
 * Relic powers are game design, NOT mathematical corollaries of theorem names.
 * The phone executes JS, not the Lean kernel; the provenance is test-audited. */
(function(root,factory){
  const api=factory();
  if(typeof module==="object"&&module.exports)module.exports=api;
  root.Rogue465=api;
})(globalThis,function(){
  const W=9,DEPTH=3,MAX_SLOTS=5;
  const EDGES=[[0,4],[1,4],[4,5],[4,5],[5,2],[5,3]];
  const DIRS=[[0,-1],[1,0],[0,1],[-1,0]];
  const EFFECTS={
    force:"攻撃 +",guard:"防御 +",focus:"観測打撃 +",charge:"最大気力 +",
    vital:"最大生命 +",ripple:"衝撃波 +",siphon:"撃破回復 +",
    pierce:"解析追撃 +",stride:"移動回復 +",luck:"撃破資金 +"
  };
  const FAMILY_EFFECTS={
    probe:["focus","pierce","luck"],ward:["guard","vital","siphon"],
    edge:["force","pierce","stride"],pulse:["ripple","charge","siphon"],
    vigor:["vital","charge","luck"],strike:["force","pierce","ripple"]
  };
  let CATALOG=null;
  function installCatalog(json){
    if(!json||!Array.isArray(json.cards)||json.cards.length!==465)
      throw Error("A catalog of exactly 465 baseline theorems is required");
    if(json.counts?.elastica!==214||json.counts?.linearInput!==251||json.counts?.declarations!==509)
      throw Error("Wrong initial theorem baseline");
    const names=new Set(),ids=new Set();
    for(const item of json.cards){
      if(!item.name||names.has(item.name)||ids.has(item.id)||!FAMILY_EFFECTS[item.family])
        throw Error("Invalid, duplicate, or untyped theorem card");
      names.add(item.name);ids.add(item.id);
    }
    CATALOG=json.cards;return CATALOG.length;
  }
  function catalog(){if(!CATALOG)throw Error("installCatalog first");return CATALOG;}
  function hash(a){const str=String(a);let x=2166136261;
    for(let i=0;i<str.length;i++)x=Math.imul(x^str.charCodeAt(i),16777619);
    return x>>>0;}
  function randStream(seed){let v=hash(seed)|0;return function(n){
    v^=v<<13;v^=v>>>17;v^=v<<5;return (v>>>0)%n;};}
  function theorem(id){const card=catalog()[id];if(!card)throw Error("invalid theorem id");return card;}
  function relic(id){const t=theorem(id),x=hash(t.name),pool=FAMILY_EFFECTS[t.family];
    const type=pool[x%pool.length],power=1+((x>>>14)%2);
    return {...t,effect:type,power,description:EFFECTS[type]+(type==="vital"?power*2:power)};}
  function stats(s){const buff={force:0,guard:0,focus:0,charge:0,vital:0,ripple:0,siphon:0,pierce:0,stride:0,luck:0};
    for(const id of s.equipment){const item=relic(id);buff[item.effect]+=item.power;}
    return {buff,maxHp:18+2*buff.vital,maxEnergy:5+buff.charge,
      attack:2+buff.force,armor:Math.min(2,buff.guard),spell:2+buff.ripple};}
  function key(depth,v,layer){return depth+":"+v+":"+layer;}
  function roomKey(s){return key(s.depth,s.vertex,s.layer);}
  function current(s){return s.rooms[roomKey(s)];}
  function tile(x,y){return y*W+x;}
  function inside(x,y){return Number.isInteger(x)&&Number.isInteger(y)&&x>0&&x<W-1&&y>0&&y<W-1;}
  function free(room,x,y){return inside(x,y)&&room.map[tile(x,y)]===0;}
  function manhattan(a,b){return Math.abs(a.x-b.x)+Math.abs(a.y-b.y);}
  function living(room){return room.enemies.filter(e=>e.hp>0);}
  function hasEnemies(s){return living(current(s)).length>0;}
  function roomSeed(s,v,layer){return s.seed+":depth"+s.depth+":room"+v+":layer"+layer;}
  function rule481(c,n,e,so,w){const score=c+2*(n+e+so+w);
    return (score===0||score===5||score===6||score===7||score===8)?1:0;}
  function sporesNext(before){const at=(x,y)=>before[((y+W)%W)*W+((x+W)%W)];
    return before.map((_,i)=>{const x=i%W,y=Math.floor(i/W);
      return rule481(at(x,y),at(x,y-1),at(x+1,y),at(x,y+1),at(x-1,y));});}
  function enemyType(v,depth,index,rng){
    const types=["moth","guard","stalker"],kind=types[(rng(997)+v+index+depth)%3];
    const hp=kind==="guard"?5+2*depth:kind==="stalker"?4+depth:3+depth;
    return {id:index,kind,x:1,y:1,hp,maxHp:hp,attack:kind==="guard"?2:1,
      scanned:false,windup:false,weakness:rng(5)-2};}
  function generateRoom(s,v,layer){
    const rng=randStream(roomSeed(s,v,layer));
    const map=Array.from({length:W*W},(_,i)=>inside(i%W,Math.floor(i/W))?0:1);
    for(const [x,y] of [[2,2],[6,2],[2,6],[6,6],[3,3],[5,5]])
      if(rng(3)===0)map[tile(x,y)]=1;
    const sand=map.map(wall=>wall?0:rng(4));
    const sporeRoom=s.depth>1&&(v===2||v===3||v===5);
    const spores=sporeRoom?map.map(wall=>wall?0:Number(rng(13)===0)):null;
    const entry=s.depth===1&&v===0&&layer===0;
    const boss=s.depth===DEPTH&&v===3&&layer===1;
    const count=entry?0:boss?1:1+(s.depth>1?1:0)+(rng(4)===0?1:0);
    const positions=[[1,1],[7,7],[7,1],[1,7],[1,4],[7,4],[4,1],[4,7],[3,6],[6,3]];
    const enemies=[];
    if(boss){enemies.push({id:0,kind:"warden",x:6,y:6,hp:22,maxHp:22,attack:3,
        weakness:1,scanned:false,windup:false});}
    else for(let i=0;i<count;i++){
      const foe=enemyType(v,s.depth,i,rng);
      let pos=positions[(i*3+rng(positions.length))%positions.length];
      if(!free({map},pos[0],pos[1])||enemies.some(e=>e.x===pos[0]&&e.y===pos[1]))
        pos=positions.find(p=>free({map},p[0],p[1])&&!enemies.some(e=>e.x===p[0]&&e.y===p[1]))||[1,1];
      foe.x=pos[0];foe.y=pos[1];enemies.push(foe);
    }
    return {map,sand,spores,enemies,claimed:false,lastFired:[],topples:0,entries:0,boss};
  }
  function append(s,message){s.log.unshift(message);if(s.log.length>14)s.log.length=14;return s;}
  function offer(s){
    if(s.offer||s.status!=="play")return;
    const selected=new Set(s.equipment),opts=[];
    const random=randStream(roomKey(s)+":"+s.seed+":"+s.turn+":"+(s.offersMade++));
    let attempts=0;
    while(opts.length<3&&attempts++<10000){
      const id=random(465);
      if(!selected.has(id)){selected.add(id);opts.push(id);}
    }
    if(opts.length!==3)throw Error("unable to choose three relics");
    s.offer=opts;append(s,"定理遺物を発見。3つから1つを選ぶ。");
  }
  function newGame(seed=4271){
    catalog();const s={seed:seed>>>0,depth:1,vertex:0,layer:0,sign:[0,0,0,0,0,0],
      rooms:{},hero:{x:4,y:4,hp:18,energy:5,insight:0,coins:0,kills:0,input:1,curve:0,heading:null},
      equipment:[],offer:null,offersMade:0,turn:0,status:"play",log:[],
      scans:0,topplings:0,roomsCleared:0,score:0};
    s.rooms[roomKey(s)]=generateRoom(s,0,0);current(s).entries++;
    offer(s);append(s,"目標：層1の右端へ進み、3階層目の番人を倒す。");
    return s;
  }
  function withClone(s){return JSON.parse(JSON.stringify(s));}
  function selectRelic(state,id,slot=0){
    if(!state.offer||!state.offer.includes(id)||state.status!=="play")return state;
    const s=withClone(state),before=stats(s);
    if(s.equipment.length<MAX_SLOTS)s.equipment.push(id);
    else{if(!Number.isInteger(slot)||slot<0||slot>=MAX_SLOTS)return state;s.equipment[slot]=id;}
    const after=stats(s);
    s.hero.hp=Math.min(after.maxHp,s.hero.hp+Math.max(0,after.maxHp-before.maxHp));
    s.hero.energy=Math.min(after.maxEnergy,s.hero.energy+Math.max(0,after.maxEnergy-before.maxEnergy));
    s.offer=null;current(s).claimed=true;
    append(s,"取得："+relic(id).name+" ／ "+relic(id).description);
    return s;
  }
  function moveOne(e,room,hero){
    const blocked=new Set(living(room).filter(x=>x!==e).map(x=>tile(x.x,x.y)));
    const src=tile(e.x,e.y),dest=tile(hero.x,hero.y),queue=[src],parent=Array(W*W).fill(-1);
    parent[src]=src;
    for(let i=0;i<queue.length;i++){
      const node=queue[i];if(node===dest)break;const x=node%W,y=Math.floor(node/W);
      for(const [dx,dy] of DIRS){
        const nx=x+dx,ny=y+dy;
        if(!free(room,nx,ny))continue;
        const nb=tile(nx,ny);if(parent[nb]!==-1||blocked.has(nb))continue;
        parent[nb]=node;queue.push(nb);
      }
    }
    if(parent[dest]===-1)return;
    let x=dest;while(parent[x]!==src&&x!==src)x=parent[x];
    const nx=x%W,ny=Math.floor(x/W);
    if(nx!==hero.x||ny!==hero.y){e.x=nx;e.y=ny;}
  }
  function die(s){if(s.hero.hp<=0){s.hero.hp=0;s.status="dead";append(s,"冒険はここで終わった。遺物も失われる。");}}
  function recordKill(s,e){
    if(e.hp>0||e.rewarded)return;e.rewarded=true;
    const b=stats(s).buff;s.hero.kills++;s.hero.insight++;
    s.hero.coins+=2+b.luck;s.hero.energy=Math.min(stats(s).maxEnergy,s.hero.energy+1);
    s.hero.hp=Math.min(stats(s).maxHp,s.hero.hp+Math.min(2,b.siphon));
    append(s,(e.kind==="warden"?"番人":"敵")+"を倒した。洞察+1。");
  }
  function avalanche(s,idx,amount){
    const room=current(s);room.sand[idx]+=amount;const firings=Array(W*W).fill(0);
    let rounds=0;
    for(;rounds<512;rounds++){
      const active=[];for(let i=0;i<W*W;i++)
        if(room.sand[i]>=4&&room.map[i]===0)active.push(i);
      if(active.length===0)break;
      for(const i of active){firings[i]++;room.sand[i]-=4;}
      for(const i of active){
        const x=i%W,y=Math.floor(i/W);
        for(const [dx,dy] of DIRS)if(free(room,x+dx,y+dy))room.sand[tile(x+dx,y+dy)]++;
      }
    }
    if(rounds===512)throw Error("stabilization exceeded its guard bound");
    room.lastFired=[];for(let i=0;i<firings.length;i++)if(firings[i]>0)room.lastFired.push(i);
    const count=firings.reduce((a,b)=>a+b,0);s.topplings+=count;room.topples+=count;
    if(count>0){
      for(const e of living(room)){
        const n=firings[tile(e.x,e.y)];
        if(n>0){e.hp=Math.max(0,e.hp-Math.min(3,n));recordKill(s,e);}
      }
      const playerHits=firings[tile(s.hero.x,s.hero.y)];
      if(playerHits>0)s.hero.hp-=Math.max(0,Math.min(2,playerHits)-stats(s).armor);
      append(s,"砂が"+count+"回崩壊。連鎖が周囲を襲う。");
    }
    return count;
  }
  function enemyPhase(s){
    const room=current(s),b=stats(s);
    for(const e of living(room)){
      if(s.status!=="play")break;
      if(e.windup){
        if(manhattan(e,s.hero)===1){
          const damage=Math.max(1,e.attack+s.depth-1-b.armor);
          s.hero.hp-=damage;append(s,"敵の予告攻撃：−"+damage+" HP");
        }else moveOne(e,room,s.hero);
        e.windup=false;
      }else if(manhattan(e,s.hero)===1)e.windup=true;
      else moveOne(e,room,s.hero);
    }
    s.turn++;
    if(room.spores&&s.turn%3===0){
      room.spores=sporesNext(room.spores);
      if(s.turn%6===0){
        if(room.spores[tile(s.hero.x,s.hero.y)]){s.hero.hp--;append(s,"規則481の胞子：−1 HP");}
        for(const e of living(room))if(room.spores[tile(e.x,e.y)]){
          e.hp=Math.max(0,e.hp-1);recordKill(s,e);
        }
      }
    }
    die(s);
    if(s.status==="play"&&living(room).length===0&&!room.claimed&&!s.offer){
      s.roomsCleared++;if(!room.boss)offer(s);
      else append(s,"番人を撃破。最終出口が開いた。");
    }
  }
  function act(state,action){
    if(state.status!=="play"||state.offer)return state;
    const s=withClone(state),hero=s.hero,room=current(s),b=stats(s);
    if(action.type==="move"){
      const dx=action.dx,dy=action.dy;
      if(!DIRS.some(d=>d[0]===dx&&d[1]===dy))return state;
      const x=hero.x+dx,y=hero.y+dy;
      if(!free(room,x,y)){append(s,"そこは壁だ。");return s;}
      const e=living(room).find(e=>e.x===x&&e.y===y);
      if(e){
        const amount=Math.max(1,b.attack+hero.input*e.weakness+
          (e.scanned?Math.max(0,2+e.weakness)+b.focus+b.pierce:0)+Math.floor(hero.curve/2));
        e.hp=Math.max(0,e.hp-amount);hero.curve=0;
        append(s,"入力"+(hero.input>0?"+":"−")+"：攻撃"+amount+" ダメージ");
        recordKill(s,e);avalanche(s,tile(x,y),2);
      }else{
        const heading=DIRS.findIndex(d=>d[0]===dx&&d[1]===dy);
        if(hero.heading!==null && hero.heading!==heading)hero.curve=Math.min(3,hero.curve+1);
        else hero.curve=Math.max(0,hero.curve-1);
        hero.heading=heading;hero.x=x;hero.y=y;
        if(b.stride&&s.turn%4===0)hero.energy=Math.min(b.maxEnergy,hero.energy+1);
      }
      enemyPhase(s);return s;
    }
    if(action.type==="polarity"){
      hero.input=hero.input===1?-1:1;
      append(s,"入力の極性を"+(hero.input===1?"+1":"−1")+"へ切り替えた。");
      return s;
    }
    if(action.type==="pulse"){
      if(hero.energy<2){append(s,"気力が足りない（必要2）。");return s;}
      hero.energy-=2;const targets=living(room).filter(e=>manhattan(e,hero)<=3);
      for(const e of targets){
        e.hp=Math.max(0,e.hp-b.spell);recordKill(s,e);
        avalanche(s,tile(e.x,e.y),4);
      }
      if(targets.length===0)avalanche(s,tile(hero.x,hero.y),4);
      append(s,"衝撃波："+b.spell+"ダメージ、砂を励起。");enemyPhase(s);return s;
    }
    if(action.type==="probe"){
      const enemies=living(room).sort((a,b)=>manhattan(a,hero)-manhattan(b,hero));
      if(!enemies.length){append(s,"観測する敵がいない。");return s;}
      const e=enemies.find(x=>!x.scanned)||enemies[0];
      const A=e.maxHp+e.attack,e0=A,e1=A-e.weakness,recovered=e0-e1;
      if(recovered!==e.weakness)throw Error("two-probe observation failed");
      e.scanned=true;e.probes=[e0,e1,recovered];
      s.scans++;hero.insight+=b.buff.focus>0?1:0;
      append(s,"二重観測：E(0)="+e0+"、E(1)="+e1+"、隠れ座標X="+recovered+"。解析追撃有効。");
      enemyPhase(s);return s;
    }
    if(action.type==="camp"){
      if(hasEnemies(s)){append(s,"敵がいる間は休めない。");return s;}
      if(hero.coins<3){append(s,"野営には資金3が必要。");return s;}
      if(hero.hp>=b.maxHp&&hero.energy>=b.maxEnergy)return state;
      hero.coins-=3;hero.hp=Math.min(b.maxHp,hero.hp+5);
      hero.energy=Math.min(b.maxEnergy,hero.energy+3);
      append(s,"野営：HPと気力を回復。");s.turn++;return s;
    }
    if(action.type==="twist"){
      if(s.vertex!==4||s.layer!==0){append(s,"接続を変更できるのは、層0の結節点4だけ。");return s;}
      if(hasEnemies(s)){append(s,"結節点の敵を倒す必要がある。");return s;}
      if(hero.insight<2){append(s,"辺反転には洞察が2必要。");return s;}
      hero.insight-=2;s.sign[3]^=1;s.turn++;
      append(s,"中央の辺3を反転。閉路の符号は"+((s.sign[2]^s.sign[3])?"奇":"偶")+"になった。");return s;
    }
    if(action.type==="travel"){
      if(hasEnemies(s)){append(s,"移動前に部屋を制圧する必要がある。");return s;}
      const i=action.edge;if(!Number.isInteger(i)||i<0||i>5)return state;
      const [a,z]=EDGES[i];if(a!==s.vertex&&z!==s.vertex)return state;
      s.vertex=s.vertex===a?z:a;s.layer^=s.sign[i];s.turn++;
      const k=roomKey(s);if(!s.rooms[k])s.rooms[k]=generateRoom(s,s.vertex,s.layer);
      current(s).entries++;hero.x=4;hero.y=4;hero.heading=null;hero.curve=0;
      append(s,"辺"+i+"から部屋"+s.vertex+"・層"+s.layer+"へ。");
      if(!hasEnemies(s)&&!current(s).claimed)offer(s);
      return s;
    }
    if(action.type==="descend"){
      if(s.vertex!==3||s.layer!==1||hasEnemies(s)){
        append(s,"次へ進むには、層1の右端で部屋を制圧する。");return s;
      }
      if(s.depth===DEPTH){
        s.status="won";s.score=1000+s.hero.kills*25+s.hero.coins*4+s.hero.hp*8-s.turn;
        append(s,"脱出成功。世界の裏側を踏破した。");return s;
      }
      s.depth++;s.vertex=0;s.layer=0;s.sign=[0,0,0,0,0,0];
      hero.x=4;hero.y=4;hero.heading=null;hero.curve=0;
      hero.hp=Math.min(b.maxHp,hero.hp+6);hero.energy=b.maxEnergy;s.turn++;
      const k=roomKey(s);if(!s.rooms[k])s.rooms[k]=generateRoom(s,0,0);
      current(s).entries++;
      if(!hasEnemies(s)&&!current(s).claimed)offer(s);
      append(s,"地下"+s.depth+"層へ降りた。接続符号は初期化された。");
      return s;
    }
    return state;
  }
  function gates(s){
    return EDGES.map(([a,b],i)=>{
      if(a!==s.vertex&&b!==s.vertex)return null;
      return {edge:i,vertex:s.vertex===a?b:a,layer:s.layer^s.sign[i],twist:!!s.sign[i]};
    }).filter(Boolean);
  }
  function progress(s){
    const count=Object.entries(s.rooms).filter(([k,room])=>
      k.startsWith(s.depth+":")&&room.enemies.every(e=>e.hp===0)).length;
    const parity=s.sign[2]^s.sign[3];
    return {roomCount:count,layerReachable:parity?12:6,parity,
      goal:s.vertex===3&&s.layer===1};
  }
  return Object.freeze({W,DEPTH,MAX_SLOTS,EDGES,DIRS,installCatalog,catalog,theorem,relic,stats,hash,
    key,roomKey,current,tile,inside,free,rule481,sporesNext,manhattan,living,hasEnemies,
    newGame,selectRelic,act,gates,progress});
});
