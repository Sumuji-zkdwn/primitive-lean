/* NEON ORBIT — iOS Safari/PWA port of the Android arcade rules. No dependencies. */
(()=>{'use strict';
const $ = id=>document.getElementById(id), cvs=$('stage'), ctx=cvs.getContext('2d',{alpha:false});
const ui={hud:$('hud'),score:$('score'),time:$('time'),best:$('best'),lives:$('lives'),timebar:$('timebar'),sound:$('sound'),pause:$('pause'),status:$('status'),overlay:$('overlay'),desc:$('overlayDesc'),stats:$('endStats'),resultScore:$('resultScore'),resultBest:$('resultBest'),resultStars:$('resultStars'),start:$('start'),help:$('overlayHelp')};
const C={dark:'#050918',blue:'#58ecff',pink:'#ff4898',red:'#ff536a',gold:'#ffd265',lime:'#8efcb5',white:'#eff5ff',muted:'#849aba'};
const rnd=(a,b)=>a+Math.random()*(b-a),clamp=(x,a,b)=>Math.max(a,Math.min(b,x)),dist=(a,b)=>Math.hypot(a.x-b.x,a.y-b.y);
const pf=n=>String(n).padStart(6,'0');
const read=(k,def)=>{try {const v=localStorage.getItem(k);return v===null?def:v}catch{return def}};
const store=(k,v)=>{try{localStorage.setItem(k,String(v))}catch{}};
let W=0,H=0,dpr=1,top=165,bottom=650,frame=0,last=0,mode='ready';
let player={x:0,y:0,vx:0,vy:0,r:12},prize=null,mines=[],parts=[],trail=[],stars=[];
let holding=false,tx=0,ty=0,score=0,best=Number(read('neon-ios-best','0'))||0,lives=3,collected=0,combo=0,timeLeft=60,playTime=0,lastCollect=-100,fever=0,invul=0,flash=0,shake=0,ambient=0,sound=read('neon-ios-sound','true')==='true',audio=null;
function beep(freq=520,duration=.07,type='sine'){
 if(!sound)return;
 try{if(!audio)audio=new(window.AudioContext||window.webkitAudioContext)();if(audio.state==='suspended')audio.resume();const osc=audio.createOscillator(),gain=audio.createGain(),t=audio.currentTime;osc.type=type;osc.frequency.setValueAtTime(freq,t);osc.frequency.exponentialRampToValueAtTime(Math.max(100,freq*.72),t+duration);gain.gain.setValueAtTime(.0001,t);gain.gain.exponentialRampToValueAtTime(.085,t+.008);gain.gain.exponentialRampToValueAtTime(.0001,t+duration);osc.connect(gain).connect(audio.destination);osc.start(t);osc.stop(t+duration+.02)}catch{}
}
function resize(){const rect=cvs.getBoundingClientRect();W=rect.width;H=rect.height;if(W<10||H<10)return;dpr=Math.min(window.devicePixelRatio||1,3);cvs.width=Math.round(W*dpr);cvs.height=Math.round(H*dpr);ctx.setTransform(dpr,0,0,dpr,0,0);
 const hudBottom=ui.hud.getBoundingClientRect().bottom-rect.top; top=Math.max(hudBottom+19,150);bottom=Math.max(top+110,H-105-parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--safe-bottom'))||H-105);bottom=Math.min(H-75,bottom);
 stars=Array.from({length:85},()=>({x:Math.random()*W,y:Math.random()*H,r:rnd(.3,1.65),phase:rnd(0,Math.PI*2)}));
 player.x=clamp(player.x||W*.5,24,W-24);player.y=clamp(player.y||((top+bottom)*.5),top+24,bottom-24);tx=player.x;ty=player.y;
 if(prize){prize.x=clamp(prize.x,45,W-45);prize.y=clamp(prize.y,top+38,bottom-38)}
}
window.addEventListener('resize',resize,{passive:true});window.addEventListener('orientationchange',()=>setTimeout(resize,150));
function spawnPrize(){let kind=Math.random()<.12?'clock':(Math.random()<.17?'fever':'gold'),x=W*.7,y=top+70;
 for(let i=0;i<100;i++){x=rnd(46,Math.max(47,W-46));y=rnd(top+42,Math.max(top+43,bottom-42));if(Math.hypot(x-player.x,y-player.y)<Math.min(120,W*.27))continue;if(mines.some(m=>Math.hypot(x-m.x,y-m.y)<66))continue;break}prize={x,y,r:19,kind};}
function addMine(){if(mines.length>=7)return;let x=W*.25,y=top+60,r=rnd(14,19);for(let i=0;i<90;i++){x=rnd(r+25,Math.max(r+26,W-r-25));y=rnd(top+30,Math.max(top+31,bottom-30));if(Math.hypot(x-player.x,y-player.y)<Math.min(130,W*.33))continue;if(prize&&Math.hypot(x-prize.x,y-prize.y)<90)continue;if(mines.some(m=>Math.hypot(x-m.x,y-m.y)<60))continue;break}const a=rnd(0,Math.PI*2),s=rnd(48,90);mines.push({x,y,vx:Math.cos(a)*s,vy:Math.sin(a)*s,r,angle:rnd(0,6.28),spin:Math.random()<.5?-1:1})}
function burst(x,y,color,n=28){for(let i=0;i<n;i++){const a=rnd(0,Math.PI*2),s=rnd(60,330),dur=rnd(.30,.84);parts.push({x,y,vx:Math.cos(a)*s,vy:Math.sin(a)*s,total:dur,left:dur,r:rnd(1.3,3.8),color})}if(parts.length>260)parts.splice(0,parts.length-260)}
function reset(){mode='play';score=0;lives=3;collected=0;combo=0;timeLeft=60;playTime=0;lastCollect=-100;fever=0;invul=0;flash=0;shake=0;holding=false;mines=[];parts=[];trail=[];player={x:W*.5,y:top+(bottom-top)*.58,vx:0,vy:0,r:12};tx=player.x;ty=player.y;spawnPrize();addMine();addMine();ui.overlay.hidden=true;beep(660,.10);updateHUD()}
function finish(){if(mode!=='play')return;mode='finish';holding=false;best=Math.max(score,best);store('neon-ios-best',best);burst(player.x,player.y,C.blue,36);beep(220,.2,'sawtooth');ui.desc.textContent=lives<=0?'GAME OVER':'TIME UP';ui.stats.hidden=false;ui.resultScore.textContent=pf(score);ui.resultBest.textContent='BEST  '+pf(best);ui.resultStars.textContent='STARS COLLECTED  '+collected;ui.start.innerHTML='RETRY <span>↻</span>';ui.help.textContent='コンボをつなげて最高得点を更新';ui.overlay.hidden=false;updateHUD()}
function collect(){const kind=prize.kind;combo=playTime-lastCollect<=4?Math.min(8,combo+1):1;lastCollect=playTime;collected++;if(kind==='clock')timeLeft=Math.min(90,timeLeft+5);if(kind==='fever')fever=Math.max(fever,5);const base=kind==='gold'?100:150;score+=base*combo*(fever>0?2:1);best=Math.max(score,best);burst(prize.x,prize.y,kind==='clock'?C.lime:kind==='fever'?C.pink:C.gold,28);flash=.12;if(collected%5===0)addMine();beep(430+Math.min(combo,8)*85,.075);navigator.vibrate?.(12);spawnPrize()}
function hit(m){if(invul>0||fever>0)return;lives--;combo=0;invul=1.65;shake=.25;flash=.22;burst(player.x,player.y,C.red,31);player.vx=-player.vx*.5+(player.x-m.x)*2;player.vy=-player.vy*.5+(player.y-m.y)*2;beep(145,.16,'sawtooth');navigator.vibrate?.(60);if(lives<=0)finish()}
function tick(dt){ambient+=dt;flash=Math.max(0,flash-dt);shake=Math.max(0,shake-dt);for(let i=parts.length-1;i>=0;i--){const p=parts[i];p.x+=p.vx*dt;p.y+=p.vy*dt;p.vx*=Math.pow(.982,dt*60);p.vy*=Math.pow(.982,dt*60);p.left-=dt;if(p.left<=0)parts.splice(i,1)}
 if(mode!=='play')return;playTime+=dt;timeLeft-=dt;fever=Math.max(0,fever-dt);invul=Math.max(0,invul-dt);if(timeLeft<=0){timeLeft=0;finish();return}
 if(holding){player.vx+=(tx-player.x)*8.2*dt;player.vy+=(ty-player.y)*8.2*dt}const drag=Math.pow(holding?.987:.994,dt*60);player.vx*=drag;player.vy*=drag;const speed=Math.hypot(player.vx,player.vy);if(speed>890){player.vx*=890/speed;player.vy*=890/speed}player.x+=player.vx*dt;player.y+=player.vy*dt;
 if(player.x-player.r<17){player.x=17+player.r;player.vx=Math.abs(player.vx)*.48}if(player.x+player.r>W-17){player.x=W-17-player.r;player.vx=-Math.abs(player.vx)*.48}if(player.y-player.r<top+5){player.y=top+5+player.r;player.vy=Math.abs(player.vy)*.48}if(player.y+player.r>bottom-5){player.y=bottom-5-player.r;player.vy=-Math.abs(player.vy)*.48}
 trail.push({x:player.x,y:player.y});if(trail.length>26)trail.shift();
 for(const m of mines){m.x+=m.vx*dt;m.y+=m.vy*dt;if(m.x-m.r<15){m.x=15+m.r;m.vx=Math.abs(m.vx)}if(m.x+m.r>W-15){m.x=W-15-m.r;m.vx=-Math.abs(m.vx)}if(m.y-m.r<top+4){m.y=top+4+m.r;m.vy=Math.abs(m.vy)}if(m.y+m.r>bottom-4){m.y=bottom-4-m.r;m.vy=-Math.abs(m.vy)}m.angle+=m.spin*dt}
 if(prize&&dist(player,prize)<=player.r+prize.r)collect();for(const m of mines){if(dist(player,m)<=player.r+m.r){hit(m);break}}
}
function circle(x,y,r,color,a=1,blur=0){ctx.beginPath();ctx.arc(x,y,Math.max(.01,r),0,Math.PI*2);ctx.fillStyle=color;ctx.globalAlpha=a;if(blur){ctx.shadowColor=color;ctx.shadowBlur=blur}ctx.fill();ctx.shadowBlur=0;ctx.globalAlpha=1}
function ring(x,y,r,color,a=.5,sw=1){ctx.beginPath();ctx.arc(x,y,r,0,Math.PI*2);ctx.strokeStyle=color;ctx.globalAlpha=a;ctx.lineWidth=sw;ctx.stroke();ctx.globalAlpha=1}
function star(x,y,r,color,rotation){ctx.beginPath();for(let j=0;j<10;j++){const a=-Math.PI/2+j*Math.PI/5+rotation,R=j%2===0?r:r*.47,xx=x+Math.cos(a)*R,yy=y+Math.sin(a)*R;j?ctx.lineTo(xx,yy):ctx.moveTo(xx,yy)}ctx.closePath();ctx.fillStyle=color;ctx.shadowColor=color;ctx.shadowBlur=14;ctx.fill();ctx.shadowBlur=0}
function draw(){if(!W||!H)return;ctx.setTransform(dpr,0,0,dpr,0,0);const g=ctx.createLinearGradient(0,0,W*.7,H);g.addColorStop(0,'#0b142e');g.addColorStop(1,C.dark);ctx.fillStyle=g;ctx.fillRect(0,0,W,H);ctx.lineWidth=.7;ctx.strokeStyle='#375889';ctx.globalAlpha=.13;ctx.beginPath();const offset=(ambient*3)%45;for(let x=offset;x<W;x+=45){ctx.moveTo(x,0);ctx.lineTo(x,H)}for(let y=0;y<H;y+=45){ctx.moveTo(0,y);ctx.lineTo(W,y)}ctx.stroke();ctx.globalAlpha=1;ctx.strokeStyle='#143f7d';ctx.globalAlpha=.43;ctx.beginPath();ctx.moveTo(19,top);ctx.lineTo(W-19,top);ctx.moveTo(19,bottom);ctx.lineTo(W-19,bottom);ctx.stroke();ctx.globalAlpha=1;
 for(const s of stars)circle(s.x,s.y,s.r,C.white,(44+58*(.5+.5*Math.sin(ambient*.8+s.phase)))/255);
 ctx.save();if(shake>0)ctx.translate(rnd(-6,6)*shake*4,rnd(-6,6)*shake*4);
 if(fever>0&&mode==='play'){ctx.fillStyle=C.pink;ctx.globalAlpha=.04;ctx.fillRect(0,top,W,bottom-top);ctx.globalAlpha=1}
 if(holding&&mode==='play'){const pulse=(ambient*85)%115;for(let i=0;i<3;i++){const rr=20+(pulse+i*38)%128;ring(tx,ty,rr,C.pink,.42*(1-(rr-20)/128),1.6)}ctx.globalAlpha=.34;ctx.strokeStyle=C.pink;ctx.lineWidth=1;ctx.beginPath();ctx.moveTo(player.x,player.y);ctx.lineTo(tx,ty);ctx.stroke();ctx.globalAlpha=1;circle(tx,ty,17,C.pink,.11);ring(tx,ty,13,C.pink,.8,1.8);ring(tx,ty,4,C.white,.75,1.2)}
 trail.forEach((t,i)=>circle(t.x,t.y,(3+(i+1)/Math.max(1,trail.length)*13)*.6,C.blue,Math.pow((i+1)/Math.max(1,trail.length),2)*.28));
 for(const p of parts){const a=clamp(p.left/p.total,0,1);circle(p.x,p.y,p.r*2.5*a,p.color,.13*a);circle(p.x,p.y,p.r*Math.max(.2,a),p.color,.9*a)}
 for(const m of mines){circle(m.x,m.y,m.r*1.9,C.red,.08,9);ring(m.x,m.y,m.r*1.28,C.red,.53,1.1);ctx.strokeStyle=C.red;ctx.lineWidth=3.2;ctx.globalAlpha=.75;ctx.lineCap='round';ctx.beginPath();for(let j=0;j<8;j++){const a=m.angle+j*Math.PI/4,u=Math.cos(a),v=Math.sin(a);ctx.moveTo(m.x+u*m.r*.7,m.y+v*m.r*.7);ctx.lineTo(m.x+u*m.r*1.47,m.y+v*m.r*1.47)}ctx.stroke();ctx.globalAlpha=1;circle(m.x,m.y,m.r*.78,C.red,.9);ring(m.x,m.y,m.r*.46,C.white,.7,1.2);circle(m.x,m.y,m.r*.15,C.dark,.96)}
 if(prize){const pp=.5+.5*Math.sin(ambient*4.3),color=prize.kind==='clock'?C.lime:prize.kind==='fever'?C.pink:C.gold;circle(prize.x,prize.y,26+pp*7,color,.075,18);ring(prize.x,prize.y,21+pp*4,color,.5,1.6);star(prize.x,prize.y,12+pp*1.6,color,ambient*.22);circle(prize.x,prize.y,3.7,C.white);if(prize.kind!=='gold'){ctx.fillStyle=color;ctx.textAlign='center';ctx.font='bold 11px system-ui';ctx.fillText(prize.kind==='clock'?'+5s':'2×',prize.x,prize.y+36)}}
 if(!(invul>0&&Math.floor(ambient*13)%2===0)){const pulse=.5+.5*Math.sin(ambient*5),r=player.r;circle(player.x,player.y,r*2.8+pulse*4,C.blue,.07,20);circle(player.x,player.y,r*2,C.blue,.14);ring(player.x,player.y,r*1.53,C.blue,.46,1.2);circle(player.x,player.y,r,C.blue,1,12);circle(player.x-r*.2,player.y-r*.25,r*.42,C.white,.95);if(fever>0)ring(player.x,player.y,r*1.95,C.pink,.87,2.1);if(invul>0)ring(player.x,player.y,r*2.15,C.gold,.82,1.8)}
 if(flash>0){ctx.fillStyle=invul>0?C.red:C.white;ctx.globalAlpha=flash*.4;ctx.fillRect(0,top,W,bottom-top);ctx.globalAlpha=1}ctx.restore()}
function updateHUD(){ui.score.textContent=pf(score);ui.time.textContent=timeLeft.toFixed(1);ui.best.textContent=pf(best);ui.time.style.color=timeLeft<10&&mode==='play'?C.red:C.blue;ui.lives.querySelectorAll('i').forEach((el,i)=>el.classList.toggle('off',i>=lives));ui.timebar.style.width=clamp(timeLeft/60*100,0,100)+'%';ui.timebar.style.background=fever>0?C.pink:C.blue;ui.sound.textContent=sound?'SFX ON':'SFX OFF';ui.sound.style.color=sound?C.lime:C.muted;ui.status.textContent=mode==='play'&&fever>0?`FEVER ×2   ${fever.toFixed(1)}s`:mode==='play'&&combo>1&&playTime-lastCollect<4?`COMBO ×${combo}`:`WAVE ${String(Math.floor(collected/5)+1).padStart(2,'0')}`;ui.status.style.color=fever>0?C.pink:combo>1?C.gold:C.blue}
function animate(now){if(!last)last=now;const dt=clamp((now-last)/1000,0,.035);last=now;tick(dt);draw();if(frame++%3===0)updateHUD();requestAnimationFrame(animate)}
function togglePause(){if(mode==='play'){mode='pause';holding=false;ui.desc.textContent='PAUSED';ui.stats.hidden=true;ui.start.innerHTML='RESUME <span>▶</span>';ui.help.textContent='指を休めても、宇宙は逃げない。';ui.overlay.hidden=false}else if(mode==='pause'){mode='play';ui.overlay.hidden=true}}
ui.start.addEventListener('click',()=>{if(mode==='pause'){togglePause()}else{reset()}});
ui.pause.addEventListener('click',e=>{e.stopPropagation();togglePause()});
ui.sound.addEventListener('click',e=>{e.stopPropagation();sound=!sound;store('neon-ios-sound',sound);if(sound)beep(640,.07);updateHUD()});
function point(e){const r=cvs.getBoundingClientRect();return{x:e.clientX-r.left,y:e.clientY-r.top}}
cvs.addEventListener('pointerdown',e=>{if(mode!=='play')return;e.preventDefault();const p=point(e);holding=true;tx=clamp(p.x,20,W-20);ty=clamp(p.y,top+20,bottom-20);cvs.setPointerCapture(e.pointerId)});
cvs.addEventListener('pointermove',e=>{if(mode!=='play'||!holding)return;e.preventDefault();const p=point(e);tx=clamp(p.x,20,W-20);ty=clamp(p.y,top+20,bottom-20)});
for(const ev of ['pointerup','pointercancel','lostpointercapture'])cvs.addEventListener(ev,()=>holding=false);
document.addEventListener('visibilitychange',()=>{last=0;if(document.hidden&&mode==='play')togglePause()});
window.addEventListener('pagehide',()=>{holding=false;if(mode==='play')togglePause()});
window.addEventListener('keydown',e=>{if(e.key==='Escape'||e.key===' '){e.preventDefault();togglePause()}});
resize();updateHUD();requestAnimationFrame(animate);
if('serviceWorker'in navigator&&location.protocol==='https:')navigator.serviceWorker.register('./sw.js').catch(()=>{});
window.NEON_ORBIT={rules:{nextCombo:(oldCombo,delta)=>delta<=4?Math.min(8,oldCombo+1):1,points:(base,combo,fever)=>base*clamp(combo,1,8)*(fever?2:1)},version:'1.0.0'};
})();
