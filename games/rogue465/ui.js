"use strict";
(function(){
  const E=globalThis.Rogue465;
  if(!E)throw Error("Rogue465 engine is missing");
  const $=(id)=>document.getElementById(id);
  const escapeHTML=s=>String(s).replace(/[&<>"']/g,c=>
    ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
  const icons={moth:"✦",guard:"▣",stalker:"◆",warden:"♛"};
  const storeKey="primitive-rogue465-save-v1";
  let state=null,replaceSlot=0,help=false,swipeStart=null,ignoreTap=false;
  function save(){
    try{globalThis.localStorage?.setItem(storeKey,JSON.stringify(state));}catch(_){}
  }
  function restore(){
    try{
      const str=globalThis.localStorage?.getItem(storeKey);
      if(!str)return null;
      const obj=JSON.parse(str);
      if(obj && obj.rooms && obj.hero && obj.seed!==undefined && obj.equipment && obj.status){
        obj.hero.input??=1;obj.hero.curve??=0;obj.hero.heading??=null;
        return obj;
      }
    }catch(_){}
    return null;
  }
  function newRun(){
    const seed=(Math.floor(Math.random()*0xffffffff)>>>0)||1;
    state=E.newGame(seed);replaceSlot=0;help=false;save();render();
  }
  function action(cmd){
    if(!state)return;
    help=false;
    const next=E.act(state,cmd);
    state=next;save();render();
  }
  function choose(id){
    if(!state||!state.offer)return;
    state=E.selectRelic(state,id,replaceSlot);
    replaceSlot=0;save();render();
  }
  function firstStepTo(x,y){
    const r=E.current(state),src=E.tile(state.hero.x,state.hero.y),goal=E.tile(x,y);
    const parent=Array(E.W*E.W).fill(-1),queue=[src];
    parent[src]=src;
    for(let i=0;i<queue.length;i++){
      const p=queue[i];if(p===goal)break;
      const px=p%E.W,py=Math.floor(p/E.W);
      for(const [dx,dy] of E.DIRS){
        const nx=px+dx,ny=py+dy;
        if(!E.free(r,nx,ny))continue;
        const t=E.tile(nx,ny);
        if(parent[t]!==-1)continue;
        parent[t]=p;queue.push(t);
      }
    }
    if(parent[goal]===-1||goal===src)return null;
    let step=goal;
    while(parent[step]!==src&&step!==src)step=parent[step];
    return {dx:(step%E.W)-state.hero.x,dy:Math.floor(step/E.W)-state.hero.y};
  }
  function renderMap(){
    const room=E.current(state),hero=state.hero,spores=room.spores,last=new Set(room.lastFired);
    const enemies=new Map(E.living(room).map(e=>[E.tile(e.x,e.y),e]));
    const html=[];
    for(let y=0;y<E.W;y++)for(let x=0;x<E.W;x++){
      const idx=E.tile(x,y),wall=room.map[idx]===1,foe=enemies.get(idx);
      const isHero=hero.x===x&&hero.y===y;
      const classes=["cell"];
      if(wall)classes.push("wall");
      if(!wall&&spores&&spores[idx])classes.push("spore");
      if(last.has(idx))classes.push("fired");
      if(foe){classes.push("enemy");if(foe.windup)classes.push("windup");
        if(foe.scanned)classes.push("scanned");if(foe.kind==="warden")classes.push("boss");}
      if(isHero)classes.push("hero");
      const body=wall?"":isHero?"◈":foe?icons[foe.kind]:"";
      const sand=wall?"":'<span class="grain">'+room.sand[idx]+"</span>";
      const aria=wall?"壁":isHero?"自分":foe?"敵、生命"+foe.hp+"、"+(foe.windup?"次に攻撃":"移動中"):"空きマス";
      html.push('<button type="button" class="'+classes.join(" ")+'" data-x="'+x+'" data-y="'+y+
        '" aria-label="('+x+','+y+') '+aria+'" '+(wall?"disabled":"")+'>'+body+sand+"</button>");
    }
    $("board").innerHTML=html.join("");
    $("board").querySelectorAll("[data-x]").forEach(el=>el.addEventListener("click",()=>{
      if(ignoreTap){ignoreTap=false;return;}
      if(state.offer||state.status!=="play")return;
      const step=firstStepTo(Number(el.dataset.x),Number(el.dataset.y));
      if(step)action({type:"move",dx:step.dx,dy:step.dy});
    }));
  }
  function renderGear(){
    $("gear").innerHTML=Array.from({length:E.MAX_SLOTS},(_,i)=>{
      const id=state.equipment[i];
      if(id===undefined)return '<div class="equipment"><b>'+String(i+1)+
        '</b><span class="name">空の装備枠</span></div>';
      const item=E.relic(id),name=item.name.split(".").pop();
      return '<div class="equipment" title="'+escapeHTML(item.name)+'"><b>'+String(i+1)+
        '</b><span class="name">'+escapeHTML(name)+'</span><span class="effect">'+
        escapeHTML(item.description)+"</span></div>";
    }).join("");
  }
  function renderGates(){
    const exits=E.gates(state),locked=E.hasEnemies(state)||!!state.offer||state.status!=="play";
    $("gates").innerHTML=exits.map(g=>{
      const dest="部屋"+g.vertex+"・層"+g.layer;
      return '<button class="door" type="button" data-edge="'+g.edge+'" '+(locked?"disabled":"")+
        '>辺'+g.edge+(g.twist?"（反転）":"")+'<small>進む → '+dest+"</small></button>";
    }).join("");
    $("gates").querySelectorAll("[data-edge]").forEach(el=>el.addEventListener("click",()=>
      action({type:"travel",edge:Number(el.dataset.edge)})));
  }
  function renderModal(){
    const modal=$("modal"),panel=$("modal-panel");
    if(help){
      modal.classList.add("visible");panel.innerHTML=
        '<h2>遊び方</h2><p>3階層を探索し、3階層目の層1・部屋3にいる番人を倒して脱出してください。'+
        '隣のマスをタップ、または十字キーで移動。敵のいるマスへ進むと攻撃します。</p>'+
        '<p>敵は予告後に攻撃します。衝撃波は気力2で周囲を攻撃し、砂を崩壊させます。'+
        '二重観測で敵の隠れた座標を復元すると解析追撃が有効になります。</p>'+
        '<p>各部屋を制圧すると、初期465定理から選ばれた遺物を一つ獲得。'+
        '層0の部屋4では洞察2を消費して辺3を反転でき、別の層へ進めます。'+
        '装備は最大5件。死亡するとその探索は終わりです。</p>'+
        '<p>定理名・出典は正規の初期465台帳に基づきますが、装備の数値効果はゲーム用の設計です。</p>'+
        '<button class="reward" type="button" id="close-help">ゲームへ戻る</button>';
      $("close-help").addEventListener("click",()=>{help=false;renderModal();});
      return;
    }
    if(state.status!=="play"){
      modal.classList.add("visible");
      panel.innerHTML='<div class="finish"><h2>'+(state.status==="won"?"脱出成功":"探索終了")+
        '</h2><p>地下'+state.depth+'階・'+state.turn+'手・撃破'+state.hero.kills+
        '体・遺物'+state.equipment.length+'件<br>'+(state.status==="won"?"最終得点 "+state.score:"死亡したら最初から。")+
        '</p><button type="button" id="again">新しい探索を始める</button></div>';
      $("again").addEventListener("click",newRun);
      return;
    }
    if(!state.offer){modal.classList.remove("visible");panel.innerHTML="";return;}
    modal.classList.add("visible");
    const full=state.equipment.length>=E.MAX_SLOTS;
    const replacement=full?'<p>装備枠が5個埋まっています。交換する枠を選んでください。</p><div class="replacers">'+
      state.equipment.map((id,i)=>'<button type="button" data-slot="'+i+
        '" aria-pressed="'+(replaceSlot===i)+'">'+String(i+1)+": "+
        escapeHTML(E.relic(id).name.split(".").pop().slice(0,12))+"</button>").join("")+"</div>":"";
    panel.innerHTML='<h2>定理遺物を発見</h2>'+
      '<p>3つのうち1つを選び、戦闘能力として身につけます。すべて初期465定理の実名です。</p>'+
      replacement+'<div class="rewards">'+state.offer.map(id=>{
        const item=E.relic(id),short=item.name.split(".").pop();
        return '<button type="button" class="reward" data-pick="'+id+'">'+
          '<strong>'+escapeHTML(short)+'</strong><span class="stat">'+escapeHTML(item.description)+
          '</span><span class="provenance">'+escapeHTML(item.name)+'<br>'+escapeHTML(item.file)+
          ':'+item.line+'</span></button>';
      }).join("")+"</div><p>この能力値はゲーム設計であり、定理の数学的な含意を主張しません。</p>";
    panel.querySelectorAll("[data-slot]").forEach(el=>el.addEventListener("click",()=>{
      replaceSlot=Number(el.dataset.slot);renderModal();
    }));
    panel.querySelectorAll("[data-pick]").forEach(el=>el.addEventListener("click",()=>
      choose(Number(el.dataset.pick))));
  }
  function render(){
    if(!state)return;
    const st=E.stats(state),room=E.current(state),p=E.progress(state);
    $("hp").textContent=state.hero.hp+" / "+st.maxHp;
    $("energy").textContent=state.hero.energy+" / "+st.maxEnergy;
    $("insight").textContent=state.hero.insight+" / "+state.hero.coins;
    $("floor").textContent=state.depth+" / "+E.DEPTH;
    $("location").textContent="部屋"+state.vertex+" · 層"+state.layer;
    const count=E.living(room).length;
    $("status").textContent=state.status==="play"?(count?"敵 "+count+"体":"制圧済")+"・"+state.turn+"手・曲率"+state.hero.curve:
      (state.status==="won"?"脱出成功":"死亡");
    $("topology").textContent="中央閉路："+(p.parity?"奇（12状態に到達可能）":"偶（6状態に限定）")+
      " ／ 現在は層"+state.layer+"。反転した辺の通過時に層が変わります。";
    renderMap();renderGates();renderGear();
    $("log").innerHTML=state.log.slice(0,8).map(x=>"<li>"+escapeHTML(x)+"</li>").join("");
    document.querySelectorAll("[data-move]").forEach(el=>{el.disabled=state.status!=="play"||!!state.offer;});
    for(const id of ["pulse","probe","camp","polarity"]){$(id).disabled=state.status!=="play"||!!state.offer;}
    $("polarity").innerHTML="入力極性 "+(state.hero.input===1?"+1":"−1")+"<br><small>攻撃の傾き</small>";
    $("twist").disabled=state.status!=="play"||!!state.offer||state.vertex!==4||state.layer!==0||
      count!==0||state.hero.insight<2;
    $("descend").disabled=state.status!=="play"||!!state.offer||!p.goal||count!==0;
    $("descend").innerHTML=state.depth===E.DEPTH?"脱出する<br><small>番人を倒して</small>":
      "次の階層へ<br><small>層1・部屋3で</small>";
    renderModal();
  }
  function setupControls(){
    document.querySelectorAll("[data-move]").forEach(el=>el.addEventListener("click",()=>{
      const [dx,dy]=el.dataset.move.split(",").map(Number);action({type:"move",dx,dy});
    }));
    $("pulse").addEventListener("click",()=>action({type:"pulse"}));
    $("probe").addEventListener("click",()=>action({type:"probe"}));
    $("polarity").addEventListener("click",()=>action({type:"polarity"}));
    $("camp").addEventListener("click",()=>action({type:"camp"}));
    $("twist").addEventListener("click",()=>action({type:"twist"}));
    $("descend").addEventListener("click",()=>action({type:"descend"}));
    $("info").addEventListener("click",()=>{help=true;renderModal();});
    $("restart").addEventListener("click",()=>{
      if(globalThis.confirm?.("現在の探索を破棄して新しく始めますか？")??true)newRun();
    });
    document.addEventListener("keydown",event=>{
      if(!state||event.ctrlKey||event.metaKey||event.altKey)return;
      if(help){if(event.key==="Escape"){help=false;renderModal();}return;}
      if(state.offer){
        const n=Number(event.key);
        if(n>=1&&n<=3)choose(state.offer[n-1]);return;
      }
      if(state.status!=="play")return;
      const keys={ArrowUp:[0,-1],w:[0,-1],ArrowRight:[1,0],d:[1,0],
        ArrowDown:[0,1],s:[0,1],ArrowLeft:[-1,0],a:[-1,0]};
      const direction=keys[event.key];
      if(direction){event.preventDefault();action({type:"move",dx:direction[0],dy:direction[1]});}
      if(event.key===" "){event.preventDefault();action({type:"pulse"});}
      if(event.key==="q")action({type:"probe"});
      if(event.key==="e")action({type:"polarity"});
      if(event.key==="t")action({type:"twist"});
    });
    const board=$("board");
    board.addEventListener("pointerdown",e=>{swipeStart={x:e.clientX,y:e.clientY};});
    board.addEventListener("pointerup",e=>{
      if(!swipeStart)return;
      const dx=e.clientX-swipeStart.x,dy=e.clientY-swipeStart.y;swipeStart=null;
      if(Math.max(Math.abs(dx),Math.abs(dy))<28)return;
      ignoreTap=true;
      const direction=Math.abs(dx)>Math.abs(dy)?
        {dx:Math.sign(dx),dy:0}:{dx:0,dy:Math.sign(dy)};
      action({type:"move",...direction});
      // The synthetic click after a swipe is ignored once.
    });
  }
  async function init(){
    try{
      const embedded=$("rogue-catalog")?.textContent;
      if(embedded)E.installCatalog(JSON.parse(embedded));
      else{
        const response=await fetch("./theorems.json",{cache:"force-cache"});
        if(!response.ok)throw Error("theorem catalog HTTP "+response.status);
        E.installCatalog(await response.json());
      }
      setupControls();
      state=restore()||E.newGame(4271);render();
    }catch(err){
      $("board").textContent="定理台帳を読み込めませんでした。再読み込みしてください。";
      $("status").textContent="起動エラー";
      $("log").textContent=String(err?.message||err);
    }
  }
  init();
})();
