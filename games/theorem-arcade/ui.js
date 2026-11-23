"use strict";
(() => {
  const E=globalThis.TheoremArcade;
  if(!E)throw Error("Theorem arcade engine did not load");
  const $=(id)=>document.getElementById(id);
  const canHTML=(s)=>String(s).replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
  let activeTab="sand",caTimer=null;

  // Only the selected experiment is active; hidden cellular automata stop.
  const panels={sand:$("sand-mode"),la:$("la-mode"),ca:$("ca-mode")};
  document.querySelectorAll("[data-tab]").forEach(btn=>btn.addEventListener("click",()=>{
    if(btn.dataset.tab!=="ca") stopCA();
    activeTab=btn.dataset.tab;
    for(const [key,panel] of Object.entries(panels))panel.classList.toggle("active",key===activeTab);
    document.querySelectorAll("[data-tab]").forEach(other=>
      other.setAttribute("aria-selected",String(other.dataset.tab===activeTab)));
    if(activeTab==="ca")renderCA();
  }));

  // --- Sandpile: source = ClockAvalancheExample, including the exact 81-input trace.
  let sand=E.sandInitial(),sandHistory=[];
  const renderSand=()=>{
    $("sand-a").textContent=String(sand.topA);
    $("sand-b").textContent=String(sand.topB);
    $("sand-round").textContent=sand.round+"回";
    const oa=E.sandObserve(sand.a),ob=E.sandObserve(sand.b);
    const same=oa.join(",")===ob.join(",");
    $("sand-observe").textContent=same?"一致":"不一致";
    $("sand-readings").textContent="A観測 ["+oa.join(", ")+"] ／ B観測 ["+ob.join(", ")+"]";
    if(sand.failed) $("sand-message").textContent="実行を停止しました："+sand.failed;
    else if(sand.round===81 && sand.topA===95 && sand.topB===158)
      $("sand-message").textContent="証明された分岐：観測は同じ、崩壊回数は95対158！";
    else if(sand.round===80 && sand.topA===95 && sand.topB===95)
      $("sand-message").textContent="80回時点では崩壊回数も95対95。次の一手を試そう。";
    else $("sand-message").textContent=sand.seen.length?
      "直近の投入：A "+sand.seen.at(-1)[2]+"回／B "+sand.seen.at(-1)[3]+"回崩壊。"+
      (same?" 観測値は一致。":" 観測値は不一致。"):
      "両世界に同じ砂を落とし、違いを探そう。";
    for(const label of ["a","b"]){
      const board=sand[label],last=new Set(sand[label==="a"?"lastA":"lastB"]);
      const root=$("sand-board-"+label);
      root.innerHTML=board.map((v,i)=>'<button type="button" class="v'+v+(last.has(i)?" fired":"")+
        '" data-site="'+i+'" aria-label="('+ (i%8)+','+Math.floor(i/8)+')に砂を2粒、現在'+v+'粒">'+v+"</button>").join("");
      root.querySelectorAll("[data-site]").forEach(button=>button.addEventListener("click",()=>
        sandApply(Number(button.dataset.site),2)));
    }
    $("sand-undo").disabled=sandHistory.length===0;
  };
  const rememberSand=()=>{sandHistory.push(sand);if(sandHistory.length>50)sandHistory.shift();};
  const sandApply=(site,grains)=>{
    if(sand.failed)return;
    rememberSand();
    const next=E.sandDrive(sand,site,grains);
    sand=next;
    renderSand();
  };
  $("sand-left").addEventListener("click",()=>sandApply(0,2));
  $("sand-right").addEventListener("click",()=>sandApply(7,2));
  $("sand-80").addEventListener("click",()=>{
    rememberSand();sand=E.sandWitness(80);renderSand();
  });
  $("sand-81").addEventListener("click",()=>{
    rememberSand();
    // The special move explicitly resumes the theorem's fixed 80-input prefix.
    if(sand.round!==80 || sand.topA!==95 || sand.topB!==95)
      sand=E.sandWitness(80);
    sand=E.sandDrive(sand,0,2);renderSand();
  });
  $("sand-reset").addEventListener("click",()=>{sandHistory=[];sand=E.sandInitial();renderSand();});
  $("sand-undo").addEventListener("click",()=>{
    if(sandHistory.length){sand=sandHistory.pop();renderSand();}
  });

  // --- Signed first Laakso graph: actual six labelled base edges with a doubled sheet.
  let la=E.laInitial(),selectedStart=8,laPuzzle=1;
  const NODE={0:[65,-37],1:[65,37],4:[273,0],5:[505,0],2:[712,-37],3:[712,37]};
  const drawLa=()=>{
    const reachable=new Set(E.laReachable(la,selectedStart));
    const pathPieces=[];
    for(const [x,y,edge] of E.laLift(la)){
      const a=NODE[Math.floor(x/2)],b=NODE[Math.floor(y/2)];
      const x1=a[0],y1=110+200*(x%2)+a[1],x2=b[0],y2=110+200*(y%2)+b[1];
      const bend=edge===2?-22:edge===3?22:0;
      const midX=(x1+x2)/2, midY=(y1+y2)/2+bend;
      const twist=la.signature[edge]===1;
      pathPieces.push('<path class="line '+(twist?"twist ":"")+(edge===2||edge===3?"middle":"")+
        '" d="M'+x1+' '+y1+' Q'+midX+' '+midY+' '+x2+' '+y2+
        '" aria-label="辺'+edge+(twist?"反転":"同層")+'"/>');
    }
    const circles=[];
    for(let layer=0;layer<2;layer++)for(let v=0;v<6;v++){
      const idx=2*v+layer,p=NODE[v],x=p[0],y=110+200*layer+p[1],reached=reachable.has(idx);
      const ring=idx===selectedStart?'<circle cx="'+x+'" cy="'+y+'" r="29" fill="none" stroke="#f0d196" stroke-width="4"/>':"";
      circles.push('<g data-node="'+idx+'" role="button" tabindex="0" aria-label="層'+layer+'の頂点'+v+'を起点にする">'+ring+
        '<circle class="'+(reached?"active-node":"inactive-node")+'" cx="'+x+'" cy="'+y+'" r="24"/>'+
        '<text class="node-label" x="'+x+'" y="'+y+'">'+v+'</text></g>');
    }
    $("la-graph").innerHTML='<text class="sheet-label" x="8" y="23">層 0</text>'+
      '<text class="sheet-label" x="8" y="223">層 1</text>'+pathPieces.join("")+circles.join("");
    $("la-graph").querySelectorAll("[data-node]").forEach(el=>{
      const pick=()=>{selectedStart=Number(el.dataset.node);renderLa();};
      el.addEventListener("click",pick);
      el.addEventListener("keydown",e=>{if(e.key==="Enter"||e.key===" "){e.preventDefault();pick();}});
    });
  };
  const renderLa=()=>{
    const parity=E.laParity(la),reach=E.laReachable(la,selectedStart).length;
    $("la-reach").textContent=reach+" / 12";
    $("la-parity").textContent=parity?"奇":"偶";
    $("la-message").textContent=parity?
      "一つながりの世界。中央の閉路で層が裏返り、起点から12状態へ届きます。":
      "分離した二枚の世界。到達数は6。ゲージ変換だけでは連結できません。";
    $("la-edges").innerHTML=la.signature.map((bit,i)=>
      '<button type="button" class="'+(bit?"negative":"")+'" data-edge="'+i+
      '" aria-label="辺'+i+'の符号を切り替え">辺'+i+'：'+(bit?"−":"＋")+"</button>").join("");
    $("la-vertices").innerHTML=Array.from({length:6},(_,i)=>
      '<button type="button" data-vertex="'+i+'" aria-label="頂点'+i+'のゲージを反転">頂点 '+i+"</button>").join("");
    $("la-edges").querySelectorAll("[data-edge]").forEach(el=>el.addEventListener("click",()=>{
      la=E.laToggle(la,Number(el.dataset.edge));renderLa();
    }));
    $("la-vertices").querySelectorAll("[data-vertex]").forEach(el=>el.addEventListener("click",()=>{
      la=E.laSwitch(la,Number(el.dataset.vertex));renderLa();
    }));
    drawLa();
  };
  $("la-reset").addEventListener("click",()=>{la=E.laInitial();selectedStart=8;renderLa();});
  $("la-puzzle").addEventListener("click",()=>{
    laPuzzle=(laPuzzle+1)%64;
    la=E.laInitial(Array.from({length:6},(_,i)=>(laPuzzle>>i)&1));
    selectedStart=8;renderLa();
  });

  // --- Rule 481 torus: small proven arena and larger experimental canvas.
  let ca=E.caInitial(17);
  const canvas=$("ca-canvas"),context=canvas.getContext("2d");
  const renderCA=()=>{
    $("ca-tick").textContent=String(ca.ticks);
    $("ca-count").textContent=String(E.caPopulation(ca));
    $("ca-3").setAttribute("aria-pressed",String(ca.size===3));
    $("ca-17").setAttribute("aria-pressed",String(ca.size===17));
    $("ca-play").textContent=caTimer===null?"自動再生":"一時停止";
    $("ca-message").textContent=ca.size===3?
      "3×3はLeanの鏡映・2周期の証明がある有限トーラス模型です。":
      "17×17は同じ局所規則の探索版。長期にわたる模様の性質は未証明。";
    if(!context)return;
    const n=ca.size,sz=510/n;
    context.clearRect(0,0,510,510);
    for(let i=0;i<ca.board.length;i++) {
      const x=(i%n)*sz,y=Math.floor(i/n)*sz;
      context.fillStyle=ca.board[i]?"#7eddbc":"#203d52";
      context.fillRect(x+1,y+1,Math.ceil(sz)-2,Math.ceil(sz)-2);
    }
  };
  const stopCA=()=>{if(caTimer!==null){clearInterval(caTimer);caTimer=null;}};
  const advanceCA=()=>{ca=E.caStep(ca);renderCA();};
  canvas.addEventListener("pointerdown",event=>{
    event.preventDefault();
    const rect=canvas.getBoundingClientRect();
    if(rect.width===0||rect.height===0)return;
    const x=Math.floor((event.clientX-rect.left)/rect.width*ca.size);
    const y=Math.floor((event.clientY-rect.top)/rect.height*ca.size);
    if(x>=0&&y>=0&&x<ca.size&&y<ca.size){ca=E.caFlip(ca,x,y);renderCA();}
  });
  $("ca-step").addEventListener("click",()=>{stopCA();advanceCA();});
  $("ca-play").addEventListener("click",()=>{
    if(caTimer!==null){stopCA();renderCA();return;}
    caTimer=setInterval(advanceCA,260);renderCA();
  });
  $("ca-seed").addEventListener("click",()=>{stopCA();ca=E.caFill(ca,"random",Math.floor(Math.random()*4294967296));renderCA();});
  $("ca-cross").addEventListener("click",()=>{stopCA();ca=E.caFill(ca,"cross");renderCA();});
  $("ca-mirror").addEventListener("click",()=>{stopCA();ca=E.caReflectNS(ca);renderCA();});
  $("ca-invert").addEventListener("click",()=>{stopCA();ca=E.caComplement(ca);renderCA();});
  $("ca-3").addEventListener("click",()=>{stopCA();ca=E.caInitial(3);renderCA();});
  $("ca-17").addEventListener("click",()=>{stopCA();ca=E.caInitial(17);renderCA();});
  $("ca-reset").addEventListener("click",()=>{stopCA();ca=E.caInitial(ca.size);renderCA();});

  renderSand();
  renderLa();
  renderCA();
})();
