/* SPORE POP — offline, one-finger chain-reaction arcade. No external libraries. */
(() => {
  'use strict';
  const R=window.SporeRules;
  const $=id=>document.getElementById(id);
  const canvas=$('field'),ctx=canvas.getContext('2d',{alpha:false});
  const overlay=$('overlay');
  const SAVE_KEY='spore-pop-v1';
  let saved={level:1,best:0,muted:false};
  try {saved={...saved,...JSON.parse(localStorage.getItem(SAVE_KEY)||'{}')};}catch(_){ /* private file playback */ }
  const save=()=>{try{localStorage.setItem(SAVE_KEY,JSON.stringify(saved));}catch(_){}};
  let soundCtx=null, lastNote=0, frame=0, screenW=390,screenH=620, scale=1,ox=0,oy=0,dpr=1;
  let state={mode:'menu',playing:false,paused:true,level:1,score:0,stageScore:0,
    shots:0,target:0,popped:0,count:0,spores:[],pulses:[],particles:[],labels:[],
    chain:0,bestCombo:0,lastPop:-100,flash:0,wait:0};
  const colors=R.COLORS;
  const random=R.rng(20261109), glowStars=[];
  for(let i=0;i<94;i++)glowStars.push({x:random()*390,y:random()*620,r:.2+random()*1.4,phase:random()*7});
  function resize(){
    const rect=canvas.getBoundingClientRect();
    screenW=Math.max(1,rect.width);screenH=Math.max(1,rect.height);
    dpr=Math.min(2,window.devicePixelRatio||1);
    canvas.width=Math.floor(screenW*dpr);canvas.height=Math.floor(screenH*dpr);
    scale=Math.min(screenW/390,screenH/620);
    ox=(screenW-390*scale)*.5;oy=(screenH-620*scale)*.5;
  }
  if(typeof ResizeObserver!=='undefined')new ResizeObserver(resize).observe(canvas); else window.addEventListener('resize',resize);
  resize();
  function audio(frequency=460,dur=.18,vol=.035,kind='sine'){
    if(saved.muted)return;
    try{
      const AC=window.AudioContext||window.webkitAudioContext;
      if(!AC)return;
      if(!soundCtx)soundCtx=new AC();
      if(soundCtx.state==='suspended')soundCtx.resume().catch(()=>{});
      const now=soundCtx.currentTime;
      if(now-lastNote<.028)return;
      lastNote=now;
      const osc=soundCtx.createOscillator(),gain=soundCtx.createGain();
      osc.type=kind;
      osc.frequency.setValueAtTime(frequency,now);
      osc.frequency.exponentialRampToValueAtTime(Math.max(45,frequency*.7),now+dur);
      gain.gain.setValueAtTime(.0001,now);
      gain.gain.exponentialRampToValueAtTime(Math.max(.0002,vol),now+.012);
      gain.gain.exponentialRampToValueAtTime(.0001,now+dur);
      osc.connect(gain);gain.connect(soundCtx.destination);osc.start(now);osc.stop(now+dur+.015);
    }catch(_){/* audio optional */}
  }
  function haptic(pattern){try{navigator.vibrate?.(pattern);}catch(_){}}
  function updateHud(){
    $('level').textContent=state.mode==='zen'?'∞':String(state.level).padStart(2,'0');
    $('score').textContent=String(Math.floor(state.score)).padStart(6,'0');
    $('best').textContent=String(saved.best).padStart(6,'0');
    $('shots').textContent=state.mode==='zen'?'∞':state.shots?'● '.repeat(Math.min(state.shots,7)).trim():'—';
    $('popped').textContent=state.popped;$('target').textContent=state.target;
    $('remaining').textContent=`${state.count-state.popped} LEFT`;
    $('progress-fill').style.width=`${Math.min(100,100*state.popped/Math.max(1,state.target))}%`;
    $('combo').innerHTML=`x${state.chain} <small>CHAIN</small>`;
    $('combo').classList.toggle('hidden',state.chain<3||!state.playing||frame-state.lastPop>1.3);
  }
  function setOverlay(html){overlay.innerHTML=html;overlay.classList.remove('hidden');state.paused=true;}
  function hideOverlay(){overlay.classList.add('hidden');state.paused=false;}
  function wave(level,mode,keepScore=false){
    state.mode=mode;state.playing=true;
    state.level=level;
    const wave=R.makeLevel(level,mode==='zen'?((level*31337+86421)>>>0):undefined);
    state.spores=wave.spores;
    state.count=wave.count;
    state.target=mode==='zen'?wave.count:wave.target;
    state.shots=mode==='zen'?999:wave.shots;
    state.popped=0;state.chain=0;state.lastPop=-100;state.bestCombo=0;
    state.flash=0;state.wait=0;
    state.pulses=[];state.particles=[];state.labels=[];
    if(!keepScore)state.score=0;
    state.stageScore=state.score;
    hideOverlay();updateHud();
    audio(425,.21,.03);
  }
  function start(mode){wave(mode==='zen'?1:Math.max(1,Number(saved.level)||1),mode);}
  function showHome(){state.playing=false;state.paused=true;state.mode='menu';
    overlay.innerHTML=`<div id="menu" class="menu-card">
    <div class="eyebrow"><span class="small-dot"></span> A LITTLE WORLD, ONE BIG CHAIN</div>
    <div class="hero-art"><div class="hero-glow"></div><div class="hero-spore hero-a"><i></i></div><div class="hero-spore hero-b"><i></i></div><div class="hero-spore hero-c"><i></i></div><div class="hero-ring"></div><div class="hero-petal p1"></div><div class="hero-petal p2"></div><div class="hero-petal p3"></div></div>
    <h1><span>SPORE</span> POP<span class="punct">.</span></h1><p class="tagline">ちいさな一撃。<br/>とんでもない連鎖。</p>
    <p class="description">漂う微生物をタップして、連鎖爆発を起こそう。<br/>少ないタップで目標数を開花させればクリア。</p>
    <button id="play" class="big-button">${saved.level>1?`STAGE ${String(saved.level).padStart(2,'0')} →`:'PLAY →'}</button>
    <button id="zen" class="secondary-button">∞ ZEN MODE <small>自由に連鎖を楽しむ</small></button>
    <p class="tiny-note">オフライン対応 ・ 片手で遊べる ・ 広告なし</p></div>`;
    overlay.classList.remove('hidden');
    $('play').onclick=()=>start('campaign');$('zen').onclick=()=>start('zen');
    updateHud();
  }
  function showHelp(){const wasPlaying=state.playing, wasPaused=state.paused;
    setOverlay(`<div class="menu-card">
      <div class="eyebrow">HOW TO PLAY</div>
      <div class="result-art">✳</div><h2 class="result-heading">連鎖させよう</h2>
      <p class="result-copy">画面を<strong style="color:#a7ffca">タップ</strong>すると衝撃波が広がる。微生物に当たると新しい衝撃波が生まれ、次々に連鎖するよ。</p>
      <p class="result-copy" style="margin-top:0"><span style="color:#ff7bb7">● ピンク</span> 大きな爆発　<span style="color:#ffde75">● 金</span> 特大爆発＋タップ回復<br><span style="color:#78dfff">● 青</span> 小さく素早い　<span style="color:#b99aff">● 紫</span> 高得点</p>
      <p class="result-copy">タップ回数を使い切っても、連鎖が続く限りチャンスあり。<br>ZENでは回数制限なく遊べる。</p>
      <button id="resume" class="big-button">${wasPlaying?'つづける →':'あそんでみる →'}</button>
      <button id="home" class="secondary-button">メニューへ戻る</button></div>`);
    $('resume').onclick=()=>{if(wasPlaying){hideOverlay();state.paused=wasPaused;}else start('campaign');};
    $('home').onclick=showHome;
  }
  function showResult(win){
    state.playing=false;state.paused=true;
    if(state.score>saved.best){saved.best=Math.floor(state.score);}
    if(win){saved.level=Math.max(saved.level,state.level+1);}
    save();updateHud();
    const stars=win?(state.shots>=2?3:state.shots>=1?2:1):0;
    setOverlay(`<div class="menu-card">
      <div class="eyebrow">${win?'MICRO UNIVERSE // COMPLETE':'MICRO UNIVERSE // RETRY'}</div>
      <div class="result-art ${win?'':'loss'}">${win?'✦':'◌'}</div>
      <h2 class="result-heading">${win?'BLOOM!':'SO CLOSE!'}</h2>
      <p class="result-copy">${win?`ステージ ${state.level} クリア！<br>${state.popped}個の微生物が連鎖で開花しました。`:`あと ${Math.max(0,state.target-state.popped)} 個でクリア！<br>一番密集したところを狙ってみよう。`}</p>
      ${win?`<div class="result-stars">${'★'.repeat(stars)}${'☆'.repeat(3-stars)}</div>`:''}
      <div class="result-num">${Number(state.score).toLocaleString('ja-JP')}<small>TOTAL SCORE</small></div>
      <button id="again" class="big-button">${win?'NEXT STAGE →':'RETRY →'}</button>
      <button id="home" class="secondary-button">⌂ メニューに戻る</button></div>`);
    $('again').onclick=()=>wave(win?state.level+1:state.level,'campaign',true);
    $('home').onclick=showHome;
  }
  function addPulse(x,y,type='lumen',depth=0){
    const max=R.radiusFor(type);
    state.pulses.push({x,y,type,depth,max,r:0,lastR:0,age:0,life:type==='gold'?.95:.72});
  }
  function sparkle(x,y,color,power=1){
    const n=Math.floor(12*power);
    for(let i=0;i<n;i++){
      const a=random()*Math.PI*2;
      const spd=(26+random()*115)*power;
      state.particles.push({x,y,vx:Math.cos(a)*spd,vy:Math.sin(a)*spd,
       color,r:1+random()*2.7,age:0,life:.35+random()*.7});
    }
    if(state.particles.length>800)state.particles.splice(0,state.particles.length-800);
  }
  function popup(x,y,text,color){state.labels.push({x,y,text,color,age:0,life:1.1});if(state.labels.length>18)state.labels.shift();}
  function release(x,y){
    if(!state.playing||state.paused||state.shots<=0)return;
    if(state.mode!=='zen')state.shots--;
    addPulse(x,y,'lumen',0);
    sparkle(x,y,'#a8f7d6',.44);
    state.flash=Math.min(.25,state.flash+.09);
    audio(220,.15,.05,'triangle');haptic(12);
    updateHud();
  }
  canvas.addEventListener('pointerdown',e=>{
    e.preventDefault();
    const box=canvas.getBoundingClientRect();
    const x=R.clamp((e.clientX-box.left-ox)/scale,0,390);
    const y=R.clamp((e.clientY-box.top-oy)/scale,0,620);
    release(x,y);
  },{passive:false});
  function pop(spore,pulse){
    spore.alive=false;
    state.popped++;
    if(frame-state.lastPop>1.5)state.chain=0;
    state.chain++;
    state.bestCombo=Math.max(state.bestCombo,state.chain);
    state.lastPop=frame;
    const value=R.scoreFor(spore.type,state.chain);
    state.score+=value;
    if(state.score>saved.best){saved.best=Math.floor(state.score);}
    addPulse(spore.x,spore.y,spore.type,Math.min(25,pulse.depth+1));
    sparkle(spore.x,spore.y,colors[spore.type],spore.type==='gold'?2.0:1.1);
    if(spore.type==='gold'&&state.mode!=='zen'){
      state.shots=Math.min(state.shots+1,7);
      popup(spore.x,spore.y-18,'+1 TAP!',colors.gold);
    }else if(state.chain>=3&&state.chain%4===0){
      popup(spore.x,spore.y-12,`x${state.chain} CHAIN`,colors[spore.type]);
    }
    state.flash=Math.min(.22,state.flash+.025);
    audio(290+Math.min(state.chain,18)*38,.10,.025,spore.type==='gold'?'triangle':'sine');
    if(state.chain>=8&&state.chain%5===0)haptic([7,20,12]);
    updateHud();
  }
  function update(dt){
    frame+=dt;
    if(state.paused)return;
    state.flash=Math.max(0,state.flash-dt*.6);
    for(const spore of state.spores){
      if(!spore.alive)continue;
      // Deterministic lightweight drift with wall bounce.
      const n=R.move(spore,dt);spore.x=n.x;spore.y=n.y;spore.vx=n.vx;spore.vy=n.vy;
      spore.angle+=dt*.6;
    }
    for(const p of state.pulses){
      p.lastR=p.r;p.age+=dt;
      p.r=p.max*Math.min(1,p.age/p.life);
      if(p.age>p.life)continue;
      for(const s of state.spores){
        if(!s.alive)continue;
        const dx=s.x-p.x,dy=s.y-p.y,dist=Math.hypot(dx,dy);
        if(dist<=p.r+s.r&&dist>=Math.max(0,p.lastR-s.r))pop(s,p);
      }
    }
    state.pulses=state.pulses.filter(p=>p.age<p.life);
    for(const p of state.particles){p.x+=p.vx*dt;p.y+=p.vy*dt;p.vx*=Math.pow(.93,dt*60);p.vy*=Math.pow(.93,dt*60);p.age+=dt;}
    state.particles=state.particles.filter(p=>p.age<p.life);
    for(const l of state.labels){l.y-=dt*29;l.age+=dt;}
    state.labels=state.labels.filter(l=>l.age<l.life);
    if(state.mode==='zen'){
      if(state.popped>=state.count&&state.pulses.length===0){
        if(state.wait===0)state.wait=1;
        else if((state.wait-=dt)<=0){wave(state.level+1,'zen',true);popup(195,310,'NEW CULTURE!',colors.lumen);}
      }
    }else if(state.pulses.length===0&&state.playing){
      if(state.popped>=state.target){
        if(state.wait===0)state.wait=.78;
        else if((state.wait-=dt)<=0){
          state.score+=state.level*420+state.shots*130;
          for(let i=0;i<65;i++)sparkle(random()*390,random()*620,colors[R.TYPES[Math.floor(random()*5)]],.25);
          audio(785,.40,.07);haptic([28,30,35]);showResult(true);
        }
      }else if(state.shots===0){
        if(state.wait===0)state.wait=.7;
        else if((state.wait-=dt)<=0)showResult(false);
      }else state.wait=0;
    }
    if(frame-state.lastPop>1.5&&state.chain>0){state.chain=0;updateHud();}
  }
  function drawSpore(s){
    const time=frame+s.phase;
    const p=(Math.sin(time*2.4)+1)*.5;
    const color=colors[s.type];
    ctx.save();ctx.translate(s.x,s.y);ctx.rotate(s.angle*.35);
    ctx.globalAlpha=.22;
    ctx.fillStyle=color;
    for(let i=0;i<7;i++){
      const a=i*Math.PI*2/7+time*.08;
      const r=s.r+(3+p*2);
      ctx.beginPath();ctx.ellipse(Math.cos(a)*r*.43,Math.sin(a)*r*.43,
        s.r*.72,s.r*.6,a*.25,0,Math.PI*2);ctx.fill();
    }
    ctx.globalAlpha=1;
    ctx.shadowColor=color;ctx.shadowBlur=14+p*8;
    const grad=ctx.createRadialGradient(-s.r*.35,-s.r*.4,0,0,0,s.r*1.4);
    grad.addColorStop(0,'#ecfff9');grad.addColorStop(.26,color);grad.addColorStop(.71,color+'ba');grad.addColorStop(1,'#102a38');
    ctx.fillStyle=grad;ctx.beginPath();ctx.arc(0,0,s.r,0,Math.PI*2);ctx.fill();
    ctx.shadowBlur=0;ctx.strokeStyle='#ffffff95';ctx.lineWidth=1.05;
    ctx.beginPath();ctx.arc(0,0,s.r*.86,-2.8,-.24);ctx.stroke();
    ctx.globalAlpha=.9;ctx.fillStyle='#faffee';
    ctx.beginPath();ctx.arc(-s.r*.24,-s.r*.2,s.r*.26,0,Math.PI*2);ctx.fill();
    ctx.globalAlpha=.4;
    for(let i=0;i<3;i++){
      const a=i*2.1+.5;ctx.beginPath();ctx.arc(Math.cos(a)*s.r*.57,Math.sin(a)*s.r*.56,s.r*.11,0,Math.PI*2);ctx.fill();
    }
    if(s.type==='gold'){
      ctx.globalAlpha=.65;ctx.strokeStyle=color;
      for(let i=0;i<5;i++){
        const a=i*1.26+time*.4;ctx.beginPath();ctx.moveTo(Math.cos(a)*s.r*1.2,Math.sin(a)*s.r*1.2);
        ctx.lineTo(Math.cos(a)*s.r*1.65,Math.sin(a)*s.r*1.65);ctx.stroke();
      }
    }
    ctx.restore();
  }
  function draw(){
    ctx.setTransform(dpr,0,0,dpr,0,0);
    const bg=ctx.createLinearGradient(0,0,screenW,screenH);
    bg.addColorStop(0,'#091f2a');bg.addColorStop(.65,'#071721');bg.addColorStop(1,'#0c2326');
    ctx.fillStyle=bg;ctx.fillRect(0,0,screenW,screenH);
    ctx.translate(ox,oy);ctx.scale(scale,scale);
    const b=ctx.createRadialGradient(195,245,25,195,310,420);
    b.addColorStop(0,'#0d343b');b.addColorStop(.5,'#0a202e');b.addColorStop(1,'#06131d');
    ctx.fillStyle=b;ctx.fillRect(0,0,390,620);
    ctx.lineWidth=.7;ctx.strokeStyle='#447f7e12';
    for(let x=20;x<=390;x+=38){ctx.beginPath();ctx.moveTo(x,0);ctx.lineTo(x,620);ctx.stroke();}
    for(let y=22;y<=620;y+=38){ctx.beginPath();ctx.moveTo(0,y);ctx.lineTo(390,y);ctx.stroke();}
    const glow=ctx.createRadialGradient(200+Math.sin(frame*.25)*100,260+Math.cos(frame*.26)*110,8,195,310,360);
    glow.addColorStop(0,'#3c77701c');glow.addColorStop(1,'#00121d00');ctx.fillStyle=glow;ctx.fillRect(0,0,390,620);
    for(const st of glowStars){ctx.globalAlpha=.13+(.13+.14*Math.sin(st.phase+frame*.65));ctx.fillStyle='#b4e7da';ctx.beginPath();ctx.arc(st.x,st.y,st.r,0,Math.PI*2);ctx.fill();}ctx.globalAlpha=1;
    // Suspended, drifting organic dust and membrane arcs.
    ctx.strokeStyle='#71b1ab12';ctx.lineWidth=1;
    for(let i=0;i<4;i++){
      const yy=93+i*147+Math.sin(frame*.33+i*2.7)*20;
      ctx.beginPath();ctx.ellipse(195,yy,180,34,Math.sin(frame*.12+i)*.2,0,Math.PI*2);ctx.stroke();
    }
    for(const s of state.spores)if(s.alive)drawSpore(s);
    for(const p of state.pulses){
      const f=Math.max(0,1-p.age/p.life);
      ctx.save();ctx.globalAlpha=.55*f;
      ctx.shadowColor=colors[p.type];ctx.shadowBlur=17;
      ctx.strokeStyle=colors[p.type];ctx.lineWidth=2.6+f*2;
      ctx.beginPath();ctx.arc(p.x,p.y,Math.max(1,p.r),0,2*Math.PI);ctx.stroke();
      ctx.globalAlpha=.08*f;ctx.fillStyle=colors[p.type];
      ctx.beginPath();ctx.arc(p.x,p.y,Math.max(1,p.r),0,2*Math.PI);ctx.fill();
      ctx.restore();
    }
    for(const p of state.particles){
      const f=Math.max(0,1-p.age/p.life);
      ctx.globalAlpha=f;ctx.fillStyle=p.color;ctx.shadowBlur=8;ctx.shadowColor=p.color;
      ctx.beginPath();ctx.arc(p.x,p.y,Math.max(.3,p.r*f),0,2*Math.PI);ctx.fill();
    }ctx.globalAlpha=1;ctx.shadowBlur=0;
    for(const l of state.labels){ctx.save();ctx.globalAlpha=Math.max(0,1-l.age/l.life);ctx.textAlign='center';ctx.font='900 12px system-ui';ctx.shadowColor=l.color;ctx.shadowBlur=10;ctx.fillStyle=l.color;ctx.fillText(l.text,l.x,l.y);ctx.restore();}
    if(state.flash>0){ctx.globalAlpha=state.flash;ctx.fillStyle='#c8fff0';ctx.fillRect(0,0,390,620);ctx.globalAlpha=1;}
  }
  let then=0;
  function loop(now){
    const dt=Math.min(.034,Math.max(0,(now-then)/1000||0));then=now;
    update(dt);draw();requestAnimationFrame(loop);
  }
  requestAnimationFrame(loop);
  $('sound').onclick=()=>{saved.muted=!saved.muted;save();$('sound').textContent=saved.muted?'♪':'♫';$('sound').classList.toggle('off',saved.muted);if(!saved.muted)audio(630,.22,.04);};
  $('sound').textContent=saved.muted?'♪':'♫';$('sound').classList.toggle('off',saved.muted);
  $('help').onclick=showHelp;
  $('restart').onclick=()=>{if(state.mode==='zen')wave(state.level,'zen',true);else if(state.mode==='campaign')wave(state.level,'campaign',true);else showHelp();};
  $('play').onclick=()=>start('campaign');$('zen').onclick=()=>start('zen');
  updateHud();
  // Minimal bridge for browser-level smoke testing (read only).
  window.__sporeDebug={snapshot:()=>({level:state.level,mode:state.mode,playing:state.playing,paused:state.paused,popped:state.popped,target:state.target,shots:state.shots,count:state.count,score:state.score,activePulses:state.pulses.length})};
})();
