"use strict";
(async function(){
 const A=globalThis.PrimitiveAtlas;
 if(!A)throw Error("Primitive Atlas data engine is missing");
 const $=id=>document.getElementById(id);
 const esc=s=>String(s??"").replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
 async function readData(id,file){
  const embedded=$(id)?.textContent?.trim();
  if(embedded)return JSON.parse(embedded);
  const response=await fetch("./"+file);
  if(!response.ok)throw Error("データを読み込めません: "+file+" ("+response.status+")");
  return response.json();
 }
 const [graph,sources,narratives]=await Promise.all([
  readData("atlas-graph","graph.json"),readData("atlas-proofs","proofs.json"),readData("atlas-narratives","narratives.json")
 ]);
 const model=A.createModel(graph,sources,narratives);
 const canvas=$("graph"),stage=canvas.parentElement,ctx=canvas.getContext("2d");
 if(!ctx)throw Error("Canvas 2D is required");
 const savedKey="primitive-atlas-v1";
 const pinnedRevision="d11b8963e08b0195cd3234f8b2a31788ad3903bc";
 const origin="https://github.com/Sumuji-zkdwn/primitive-lean/blob/"+pinnedRevision+"/";
 const initial=Number(new URLSearchParams(globalThis.location?.search||"").get("n"))-1;
 let selected=Number.isInteger(initial)&&initial>=0&&initial<A.SIZE?initial:229;
 let mode="focus",tab="read",zoom=1,panX=0,panY=0,linkSource=null,linkDraft=null;
 let research={ids:[],claim:""};
 let links=[],graphHitboxes=[],pointers=new Map(),pinch=null,gesture=null,suppressHit=false;
 try{
  const stored=JSON.parse(localStorage.getItem(savedKey)||"{}");
  links=A.sanitizeLinks(model,stored.links||[]);
  research=A.sanitizeResearch(model,stored.research);
  if(!(Number.isInteger(initial)&&initial>=0&&initial<A.SIZE)&&Number.isInteger(stored.selected)&&stored.selected>=0&&stored.selected<A.SIZE)
   selected=stored.selected;
 }catch(_){}
 function persist(){
  try{localStorage.setItem(savedKey,JSON.stringify({selected,links,research}));}catch(_){}
 }
 function onMobile(){return (globalThis.innerWidth??window.innerWidth??1200)<=900;}
 function openReader(){document.body.classList.add("reader-open");}
 function closeReader(){document.body.classList.remove("reader-open");}
 function moveSelection(id,options={}){
  if(!Number.isInteger(id)||id<0||id>=A.SIZE)return;
  if(linkSource!==null&&linkSource!==id&&!options.ignoreLink){
   linkDraft={from:linkSource,to:id,note:""};
   linkSource=null;
   tab="deps";renderReader();openReader();return;
  }
  selected=id;mode="focus";zoom=1;panX=0;panY=0;tab="read";
  persist();updateHistory();render();if(options.open!==false&&onMobile())openReader();
 }
 function updateHistory(){
  try{
   const url=new URL(globalThis.location.href);
   url.searchParams.set("n",String(selected+1));
   history.replaceState(null,"",url.toString());
  }catch(_){}
 }
 function renderSearch(query){
  const hits=$("hits"),matches=A.search(model,query,30);
  if(!query.trim()){hits.hidden=true;hits.innerHTML="";return;}
  hits.hidden=false;
  hits.innerHTML=matches.length?matches.map(({id})=>{
   const n=model.nodes[id],p=model.proofs[id];
   return '<button type="button" class="hit" data-hit="'+id+'"><span>'+
    esc(model.argumentsById[id]?.title||n.label)+'<small>'+esc(n.chapter)+' · 前提 '+n.parents.length+'件'+
    (model.argumentsById[id]?" · 日本語の論証あり":p.comment?" · 原文の説明あり":"")+
    '</small></span><span class="mono">#'+String(id+1).padStart(3,"0")+'</span></button>';
  }).join(""):'<div class="empty" style="padding:13px">一致する定理がありません。</div>';
  hits.querySelectorAll("[data-hit]").forEach(el=>el.addEventListener("click",()=>{
   $("search").value="";renderSearch("");
   moveSelection(Number(el.dataset.hit));
  }));
 }
 const canvasSize=()=>{const rect=stage.getBoundingClientRect();return {w:Math.max(250,rect.width),h:Math.max(190,rect.height)};};
 function layout(){
  const points=mode==="all"?new Map(model.overview):A.focus(model,selected,2);
  if(mode!=="all"){
   const connected=links.filter(l=>l.from===selected||l.to===selected);
   let after=0,before=0;
   for(const link of connected){
    const other=link.from===selected?link.to:link.from;
    if(points.has(other))continue;
    if(link.from===selected)points.set(other,{x:675,y:-60+after++*46});
    else points.set(other,{x:-675,y:-60+before++*46});
   }
  }
  return points;
 }
 function nodeRadius(scale,id){
  return mode==="all"?Math.max(1.5,Math.min(8,7*scale)):id===selected?9:6.7;
 }
 function draw(){
  const {w,h}=canvasSize(),dpr=Math.min(2,globalThis.devicePixelRatio||1);
  canvas.width=Math.round(w*dpr);canvas.height=Math.round(h*dpr);
  canvas.style.width=w+"px";canvas.style.height=h+"px";
  ctx.setTransform(dpr,0,0,dpr,0,0);
  ctx.fillStyle="#111e28";ctx.fillRect(0,0,w,h);
  const coords=layout(),values=[...coords.values()];
  if(!values.length)return;
  const minX=Math.min(...values.map(p=>p.x)),maxX=Math.max(...values.map(p=>p.x));
  const minY=Math.min(...values.map(p=>p.y)),maxY=Math.max(...values.map(p=>p.y));
  const fit=Math.min((w-80)/(maxX-minX+180),(h-90)/(maxY-minY+100));
  const scale=Math.min(mode==="all"?1.6:1.15,Math.max(mode==="all"?.055:.25,fit))*zoom;
  const mx=(minX+maxX)/2,my=(minY+maxY)/2;
  const at=p=>({x:w/2+(p.x-mx)*scale+panX,y:h/2+(p.y-my)*scale+panY});
  // Horizontal tier guides are a quiet blueprint aid, not decorative noise.
  if(mode==="all"){
   ctx.strokeStyle="#304350";ctx.lineWidth=.8;
   for(let i=0;i<=model.graph.summary.maxDepth;i++){
    const x=at({x:i*185,y:0}).x;
    if(x<0||x>w)continue;
    ctx.beginPath();ctx.moveTo(x,0);ctx.lineTo(x,h);ctx.stroke();
   }
  }
  for(const n of model.nodes){
   const from=coords.get(n.id);if(!from)continue;
   const end=at(from);
   for(const p of n.parents){
    const point=coords.get(p);if(!point)continue;
    const start=at(point),highlight=p===selected||n.id===selected;
    ctx.lineWidth=highlight?1.85:mode==="all"?.8:1.15;
    ctx.strokeStyle=highlight?"#d9c18c":mode==="all"?"#4b6a7599":"#7ca7a7a0";
    ctx.beginPath();ctx.moveTo(start.x,start.y);
    ctx.bezierCurveTo((start.x+end.x)/2,start.y,(start.x+end.x)/2,end.y,end.x,end.y);ctx.stroke();
   }
  }
  ctx.save();ctx.setLineDash([5,6]);
  for(const link of links){
   const source=coords.get(link.from),target=coords.get(link.to);
   if(!source||!target)continue;
   const a=at(source),b=at(target);
   ctx.strokeStyle="#e2a68c";ctx.lineWidth=1.6;
   ctx.beginPath();ctx.moveTo(a.x,a.y);ctx.lineTo(b.x,b.y);ctx.stroke();
  }
  ctx.restore();
  graphHitboxes=[];
  for(const n of model.nodes){
   const pos=coords.get(n.id);if(!pos)continue;
   const point=at(pos),radius=nodeRadius(scale,n.id);
   const isPicked=n.id===selected;
   const hasExplanation=!!model.argumentsById[n.id];
   ctx.fillStyle=isPicked?"#e1c58d":hasExplanation?"#a9d4b6":
     n.school==="Elastica"?"#7eb8b9":"#719da8";
   ctx.beginPath();ctx.arc(point.x,point.y,radius,0,Math.PI*2);ctx.fill();
   if(isPicked){
    ctx.strokeStyle="#f4e3ba";ctx.lineWidth=1.5;
    ctx.beginPath();ctx.arc(point.x,point.y,radius+6,0,Math.PI*2);ctx.stroke();
   }
   if(mode==="focus"&&(isPicked||scale>.55&&radius>=6)){
    const name="#"+String(n.id+1).padStart(3,"0");
    ctx.fillStyle=isPicked?"#f6e8cb":"#b3cbd0";
    ctx.font=(isPicked?"700 13px":"11px")+" system-ui,'Noto Sans JP',sans-serif";
    ctx.textAlign="left";
    const labelX=point.x+radius+8;
    if(labelX> w-70){ctx.textAlign="right";ctx.fillText(name,point.x-radius-8,point.y-8,80);}
    else ctx.fillText(name,labelX,point.y-8,80);
    ctx.textAlign="left";
   }else if(mode==="all"&&isPicked&&scale>.13){
    ctx.fillStyle="#e8d9ae";ctx.font="600 12px system-ui";ctx.fillText("#"+(n.id+1),point.x+8,point.y-6);
   }
   graphHitboxes.push({id:n.id,x:point.x,y:point.y});
  }
  ctx.textAlign="left";ctx.font="11px system-ui";
  ctx.fillStyle="#93afb4";
  ctx.fillText(mode==="all"?"465定理 / 629直接証明参照":"左：証明の前提　／　右：この定理の後続",12,19);
 }
 function nodeButton(id,desc=""){
  const n=model.nodes[id];
  return '<button class="chip" type="button" data-node="'+id+'">'+esc(model.argumentsById[id]?.title||n.label)+
   (desc?'<br><small>'+esc(desc)+'</small>':"")+'</button>';
 }
 function makeSourceLink(n,p){
  return origin+n.file+"#L"+p.line;
 }
 function argumentBody(id){
  const a=model.argumentsById[id],r=model.proofs[id],n=model.nodes[id];
  let html=a?'<p>'+esc(a.summary)+'</p><div class="section-label">成立する条件</div><p>'+esc(a.assumptions)+'</p><div class="section-label">論証の流れ</div><ol class="proof-notes">'+a.steps.map(s=>'<li>'+esc(s)+'</li>').join("")+'</ol>':
   '<p class="source-note">日本語論証は未登録です。原文から確認してください。</p>';
  if(r.comment)html+='<details class="proof-detail"><summary>原ソースの説明</summary><p>'+esc(r.comment)+'</p></details>';
  html+='<details class="proof-detail"><summary>命題・Lean証明・出典</summary><pre class="source-block">'+esc(r.statement)+'</pre><pre class="source-block">'+esc(r.proof)+'</pre><p><a target="_blank" rel="noopener" href="'+esc(makeSourceLink(n,r))+'">元のソース</a></p></details>';
  return html+'<div class="row-actions">'+nodeButton(id,"この定理に移動")+'</div>';
 }
 function renderProofPlan(n){
  const order=A.proofOrder(model,[n.id]).filter(id=>id!==n.id);
  if(!order.length)return '<p class="source-note">初期465定理内に先行する証明参照はありません。定義・外部補題を使用する場合があります。</p>';
  const direct=new Set(n.parents);
  const cards=order.map(id=>{
   const node=model.nodes[id],a=model.argumentsById[id];
   return '<details class="proof-detail proof-ancestor" data-proof-ancestor="'+id+'"><summary><span>#'+String(id+1).padStart(3,"0")+' '+esc(a?.title||A.short(node))+'</span><small>'+(direct.has(id)?"直接参照":"間接参照")+' · '+(a?"日本語論証":"原文のみ")+'</small></summary>'+argumentBody(id)+'</details>';
  }).join("");
  return '<details class="proof-detail proof-route"><summary>前提の論証を展開 · '+order.length+'件</summary><p class="source-note">元の証明が参照する先行定理を重複なく依存順に並べています。証明の必要性・十分性を新たに確立するものではありません。</p>'+cards+'</details>';
 }
 function renderRead(n,p){
  const human=model.argumentsById[n.id];
  let html="";
  if(human){
   html+='<div class="section-label">日本語で読む · 論証の概説</div><div class="claim">'+esc(human.title)+'</div>'+
    '<p>'+esc(human.summary)+'</p>'+
    '<details class="proof-detail main-argument"><summary>論証を展開 · '+human.steps.length+'段階</summary><div class="section-label">成立する条件</div><p>'+esc(human.assumptions)+'</p>'+
    '<div class="section-label">論証の流れ</div><ol class="proof-notes">'+
    human.steps.map(step=>'<li>'+esc(step)+'</li>').join("")+'</ol></details>'+
    '<p class="boundary">この説明は原文の定理と証明から作成した読み解きです。形式的証明の代わりではなく、厳密な仮定や詳細は「Lean原文」を参照してください。</p>';
  }else{
   html+='<div class="section-label">この定理の読み方</div>'+
    '<p>この定理には、人間向けの日本語論証をまだ登録していません。根拠がない文章を自動で作らず、実際の命題・原文の説明・証明内の参照を示します。</p>';
  }
  html+=renderProofPlan(n);
  html+='<details class="proof-detail"><summary>さらに詳しい日本語論証を依頼する</summary><p class="source-note">対象と直接参照先の実際のLean命題・証明を含む資料です。コピーしてChatGPT等に渡せます。このオフライン画面自体は解説を生成しません。</p><textarea class="argument-packet" id="argument-packet" readonly aria-label="論証依頼用資料">'+esc(A.argumentPacket(model,n.id))+'</textarea><div class="row-actions"><button class="action" type="button" id="copy-argument">資料をコピー／選択</button><span id="copy-argument-status" role="status" class="slim"></span></div></details>';
  if(p.comment){
   html+='<div class="section-label">原ソースに付された説明（英語）</div><p class="source-note">'+
    esc(p.comment)+'</p>';
  }
  html+='<div class="section-label">命題を確認する</div><pre class="source-block">'+esc(p.statement)+'</pre>'+
   '<div class="row-actions"><button class="action" id="go-deps" type="button">前提と後続を見る</button>'+
   '<button class="action" id="go-lean" type="button">Lean証明を開く</button><button class="action" type="button" id="add-research">構想に追加</button></div>';
  return html;
 }
 function renderDeps(n,p){
  const parents=n.parents,children=model.children[n.id];
  let html='<p class="source-note">以下の実線は、Leanの証明項が他の初期定理を直接参照するという記録です。必要条件の証明や因果関係を意味しません。</p>';
  html+='<div class="section-label">この証明が参照する定理 · '+parents.length+'件</div>'+
   (parents.length?'<div class="chips">'+parents.map(id=>nodeButton(id)).join("")+'</div>':
   '<p class="empty">初期465定理の内部には直接参照する親がありません。定義・補助定理などの参照は別に存在します。</p>');
  html+='<div class="section-label">この証明を参照する後続 · '+children.length+'件</div>'+
   (children.length?'<div class="chips">'+children.map(id=>nodeButton(id)).join("")+'</div>':
   '<p class="empty">初期465定理の範囲では直接の後続参照はありません。</p>');
  html+='<p class="slim">定義・内部補題などへの参照：'+n.otherProjectRefs.length+
   '件。これは629本の「定理→定理」の辺と区別して保持されています。</p>';
  if(parents.length){
   html+='<div class="section-label">Lean証明中の手掛かり</div>';
   for(const id of parents.slice(0,8)){
    const parent=model.nodes[id],matches=A.proofLineMatches(model,n.id,id);
    html+='<div class="source-note">'+esc(parent.label)+'</div>';
    if(matches.length)html+='<pre class="source-block">'+esc(matches.map(x=>x.text).join("\n"))+'</pre>';
    else html+='<p class="slim">型検査後の直接参照として記録されていますが、この略称の文字列は表示用の証明本文に現れません。</p>';
   }
  }
  html+='<div class="section-label">あなたの探索リンク</div>'+
   '<p class="source-note">仮説的な関連を追加できます。点線で表示し、元の証明DAGやLeanファイルは変更しません。</p>'+
   '<button class="action primary" id="begin-link" type="button">この定理から別の定理へ線を引く</button>';
  const relevant=links.filter(l=>l.from===n.id||l.to===n.id);
  html+=relevant.map(l=>{
   const other=l.from===n.id?l.to:l.from;
   return '<div class="connection"><span>↔ '+esc(model.nodes[other].label)+
    '<br><small>'+esc(l.note||"注記なし")+'</small></span>'+
    '<button type="button" data-del="'+links.indexOf(l)+'">解除</button></div>';
  }).join("");
  if(linkSource!==null)html+='<div class="link-draft"><strong>つなぐ相手を選択中</strong><p>検索またはグラフで別の定理を選んでください。正式な証明の辺にはなりません。</p>'+
   '<button class="action" id="cancel-link" type="button">キャンセル</button></div>';
  if(linkDraft){
   html+='<div class="link-draft"><strong>探索リンクのメモ</strong><p>'+
    esc(model.nodes[linkDraft.from].label)+' → '+esc(model.nodes[linkDraft.to].label)+'</p>'+
    '<textarea id="link-note" maxlength="600" placeholder="どこが関係していそうか（自由記述）">'+esc(linkDraft.note)+'</textarea>'+
    '<div class="row-actions"><button class="action primary" id="save-link">点線として保存</button>'+
    '<button class="action" id="cancel-link">取り消し</button></div></div>';
  }
  return html;
 }
 function renderResearch(n){
  let html='<div class="section-label">研究構想 · 未検証</div><p>定理を複数選び、新しい命題の仮説を記録できます。元の証明や依存線は変更しません。</p>';
  html+='<div class="row-actions"><button type="button" id="add-research" class="action primary"'+(research.ids.includes(n.id)||research.ids.length>=20?' disabled':'')+'>選択中の定理を追加</button></div>';
  html+='<div class="section-label">手掛かり · '+research.ids.length+'/20件</div>';
  html+=research.ids.length?research.ids.map(id=>'<div class="connection">'+nodeButton(id)+'<button type="button" data-remove-research="'+id+'">外す</button></div>').join(""):'<p class="empty">グラフや検索で別の定理を選択し、読み解き画面の「構想に追加」を押してください。</p>';
  html+='<label class="section-label" for="research-claim">新しい命題の候補・疑問</label><textarea class="argument-packet" id="research-claim" maxlength="3000" placeholder="例：どの仮定を緩めてもこの結論は成立するか？">'+esc(research.claim)+'</textarea>';
  html+='<div class="section-label">Lean検証に渡す</div><p class="source-note">選んだ定理と直接参照先の実際の証明、仮説、探索リンクを一つの依頼資料にします。ChatGPTに貼ってLeanへの定式化・検証を依頼できます。この画面はLeanを実行しません。</p><button type="button" id="prepare-research" class="action primary"'+(!research.ids.length?' disabled':'')+'>検証資料を作る</button><div id="research-output"></div>';
  return html;
 }
 function renderLean(n,p){
  const url=makeSourceLink(n,p);
  return '<div class="section-label">Leanの命題（原文）</div><pre class="source-block">'+esc(p.statement)+'</pre>'+
   '<div class="section-label">Leanの証明（原文）</div><pre class="source-block">'+esc(p.proof)+'</pre>'+
   '<p class="source-note">この表示は元ファイルから取り出したテキストです。型検査済みの証明参照グラフは既存の検証スナップショットから作成しています。</p>'+
   '<p><a target="_blank" rel="noopener" href="'+esc(url)+'">GitHubで元の証明を確認する</a></p>';
 }
 function renderReader(){
  const n=model.nodes[selected],p=model.proofs[selected];
  $("theorem-title").textContent=model.argumentsById[selected]?.title||A.short(n);
  $("chapter").textContent=n.chapter;
  $("number").textContent="#"+String(n.id+1).padStart(3,"0");
  $("depth").textContent="依存の深さ "+n.depth;
  $("theorem-meta").textContent=(n.school==="Elastica"?"曲線・幾何":"線形入力・観測")+
   " · 参照 "+n.parents.length+"件 · 後続 "+model.children[n.id].length+"件";
  document.querySelectorAll("[data-reader-tab]").forEach(el=>
   el.setAttribute("aria-selected",String(el.dataset.readerTab===tab)));
  const content=$("reader-content");
  content.innerHTML=tab==="read"?renderRead(n,p):tab==="deps"?renderDeps(n,p):tab==="research"?renderResearch(n):renderLean(n,p);
  content.querySelectorAll("[data-node]").forEach(el=>el.addEventListener("click",()=>{
   moveSelection(Number(el.dataset.node),{open:false});
  }));
  content.querySelectorAll("[data-del]").forEach(el=>el.addEventListener("click",()=>{
   links.splice(Number(el.dataset.del),1);persist();linkDraft=null;renderReader();draw();
  }));
  $("copy-argument")?.addEventListener("click",async()=>{
   const area=$("argument-packet"),status=$("copy-argument-status");
   if(!area)return;
   try{
    if(!globalThis.navigator?.clipboard?.writeText)throw Error("Clipboard unavailable");
    await globalThis.navigator.clipboard.writeText(area.value);
    if(status)status.textContent="コピーしました。";
   }catch(_){
    area.focus();area.select?.();area.setSelectionRange?.(0,area.value.length);
    if(status)status.textContent="選択しました。端末のコピー操作を使ってください。";
   }
  });
  $("add-research")?.addEventListener("click",()=>{
   research=A.sanitizeResearch(model,{...research,ids:[...research.ids,selected]});
   tab="research";persist();renderReader();openReader();
  });
  content.querySelectorAll("[data-remove-research]").forEach(el=>el.addEventListener("click",()=>{
   research={...research,ids:research.ids.filter(id=>id!==Number(el.dataset.removeResearch))};
   persist();renderReader();
  }));
  $("research-claim")?.addEventListener("input",e=>{
   research=A.sanitizeResearch(model,{...research,claim:e.target.value});
   persist();
   const out=$("research-output");if(out)out.innerHTML="";
  });
  $("prepare-research")?.addEventListener("click",()=>{
   if(!research.ids.length)return;
   const out=$("research-output");if(!out)return;
   out.innerHTML='<textarea class="argument-packet" id="research-packet" readonly aria-label="Lean検証依頼資料">'+esc(A.researchPacket(model,research,links))+'</textarea><div class="row-actions"><button type="button" class="action" id="copy-research">資料をコピー／選択</button><span id="copy-research-status" class="slim" role="status"></span></div>';
   $("copy-research")?.addEventListener("click",async()=>{
    const area=$("research-packet"),status=$("copy-research-status");if(!area)return;
    try{
     if(!globalThis.navigator?.clipboard?.writeText)throw Error("Clipboard unavailable");
     await globalThis.navigator.clipboard.writeText(area.value);
     if(status)status.textContent="コピーしました。";
    }catch(_){
     area.focus();area.select?.();area.setSelectionRange?.(0,area.value.length);
     if(status)status.textContent="選択しました。端末のコピー操作を使ってください。";
    }
   });
  });
  $("go-deps")?.addEventListener("click",()=>{tab="deps";renderReader();});
  $("go-lean")?.addEventListener("click",()=>{tab="lean";renderReader();});
  $("begin-link")?.addEventListener("click",()=>{
   linkSource=selected;linkDraft=null;$("search").focus();renderReader();
  });
  $("cancel-link")?.addEventListener("click",()=>{
   linkSource=null;linkDraft=null;renderReader();
  });
  $("save-link")?.addEventListener("click",()=>{
   if(!linkDraft)return;
   linkDraft.note=$("link-note").value;
   links=A.addLink(model,links,linkDraft.from,linkDraft.to,linkDraft.note);
   linkDraft=null;linkSource=null;persist();renderReader();draw();
  });
 }
 function render(){
  $("graph-title").textContent=mode==="all"?"初期465定理の全体図":"前提から証明をたどる";
  $("graph-subtitle").textContent=mode==="all"?"629本の直接証明参照を表示":"選択中："+(model.argumentsById[selected]?.title||A.short(model.nodes[selected]));
  $("focus").setAttribute("aria-pressed",String(mode==="focus"));
  $("overview").setAttribute("aria-pressed",String(mode==="all"));
  $("open-reader").textContent="定理 #"+String(selected+1).padStart(3,"0")+" を読む ↑";
  renderReader();draw();
 }
 function resetView(next=mode){
  mode=next;zoom=1;panX=0;panY=0;render();
 }
 function bind(){
  $("focus").addEventListener("click",()=>resetView("focus"));
  $("overview").addEventListener("click",()=>resetView("all"));
  $("zoom-reset").addEventListener("click",()=>resetView());
  $("open-reader").addEventListener("click",openReader);
  $("close-reader").addEventListener("click",closeReader);
  document.querySelectorAll("[data-reader-tab]").forEach(el=>el.addEventListener("click",()=>{
   tab=el.dataset.readerTab;renderReader();
  }));
  $("search").addEventListener("input",e=>renderSearch(e.target.value));
  $("search").addEventListener("keydown",e=>{
   if(e.key==="Escape"){e.target.value="";renderSearch("");e.target.blur();}
   if(e.key==="Enter"){const first=$("hits").querySelector("[data-hit]");
    if(first){e.preventDefault();first.click();}
   }
  });
  document.addEventListener("keydown",e=>{
   if(e.key==="Escape"){closeReader();$("hits").hidden=true;linkSource=null;linkDraft=null;renderReader();}
   if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==="k"){e.preventDefault();$("search").focus();}
  });
  const distance=pts=>Math.hypot(pts[0].x-pts[1].x,pts[0].y-pts[1].y);
  canvas.addEventListener("pointerdown",e=>{
   if(e.button!==undefined&&e.button!==0)return;
   e.preventDefault();canvas.setPointerCapture?.(e.pointerId);
   const id=e.pointerId??"pointer";
   pointers.set(id,{x:e.clientX,y:e.clientY});
   if(pointers.size>=2){
    pinch={distance:Math.max(1,distance([...pointers.values()].slice(0,2))),zoom};
    gesture=null;suppressHit=true;return;
   }
   gesture={id,x:e.clientX,y:e.clientY,lastX:e.clientX,lastY:e.clientY,moved:false};
  });
  canvas.addEventListener("pointermove",e=>{
   const id=e.pointerId??"pointer";
   if(pointers.has(id))pointers.set(id,{x:e.clientX,y:e.clientY});
   if(pinch&&pointers.size>=2){
    const dist=distance([...pointers.values()].slice(0,2));
    zoom=A.clamp(pinch.zoom*dist/pinch.distance,.45,16);draw();return;
   }
   if(!gesture||gesture.id!==id)return;
   const dx=e.clientX-gesture.lastX,dy=e.clientY-gesture.lastY;
   if(Math.hypot(e.clientX-gesture.x,e.clientY-gesture.y)>7)gesture.moved=true;
   if(gesture.moved){panX+=dx;panY+=dy;draw();}
   gesture.lastX=e.clientX;gesture.lastY=e.clientY;
  });
  canvas.addEventListener("pointerup",e=>{
   const id=e.pointerId??"pointer",g=gesture;
   pointers.delete(id);
   if(pinch){if(pointers.size<2)pinch=null;gesture=null;return;}
   gesture=null;
   if(suppressHit){suppressHit=false;return;}
   if(!g||g.id!==id||g.moved)return;
   const rect=canvas.getBoundingClientRect(),x=e.clientX-rect.left,y=e.clientY-rect.top;
   let best=null,dist=mode==="all"?16:26;
   for(const hit of graphHitboxes){
    const d=Math.hypot(x-hit.x,y-hit.y);
    if(d<dist){dist=d;best=hit.id;}
   }
   if(best!==null)moveSelection(best);
  });
  canvas.addEventListener("pointercancel",()=>{pointers.clear();pinch=null;gesture=null;suppressHit=false;});
  canvas.addEventListener("wheel",e=>{
   e.preventDefault();zoom=A.clamp(zoom*(e.deltaY<0?1.12:.89),.45,16);draw();
  },{passive:false});
  if(typeof ResizeObserver==="function")new ResizeObserver(draw).observe(stage);
  else globalThis.addEventListener?.("resize",draw);
 }
 bind();render();persist();
})().catch(error=>{
 const el=document.getElementById("reader-content");
 if(el)el.textContent="証明資料を読み込めませんでした: "+String(error?.message||error);
});
