/* SPORE POP deterministic game rules: shared by browser and tests. */
(function(root, factory) {
  const api = factory();
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  root.SporeRules = api;
})(typeof globalThis !== 'undefined' ? globalThis : this, function() {
  const TYPES = ['lumen','rose','azure','gold','violet'];
  const COLORS = {
    lumen:'#a7ffca', rose:'#ff7bb7', azure:'#78dfff',
    gold:'#ffde75', violet:'#b99aff'
  };
  const clamp = (n,min,max)=>Math.max(min,Math.min(max,n));
  function rng(seed) {
    let state=(seed>>>0)||0x9E3779B9;
    return function(){
      state^=state<<13; state^=state>>>17; state^=state<<5;
      return (state>>>0)/4294967296;
    };
  }
  function typeAt(level, random) {
    const t=random();
    if(level>=4 && t<0.10) return 'gold';
    if(level>=3 && t<0.22) return 'violet';
    if(level>=2 && t<0.44) return 'azure';
    if(t<0.72) return 'rose';
    return 'lumen';
  }
  function makeLevel(level, seed) {
    level=Math.max(1,Math.floor(level));
    const rand=rng(seed===undefined?(level*1000003+7127):seed);
    const count=Math.min(56,15+level*3);
    // Loose clusters reward aiming and encourage chain reactions without fixed solutions.
    const centers=[];
    for(let i=0;i<5;i++) centers.push({x:62+rand()*266,y:62+rand()*480});
    const spores=[];
    for(let i=0;i<count;i++) {
      let x,y; let tries=0;
      do {
        const c=centers[Math.floor(rand()*centers.length)];
        x=clamp(c.x+(rand()+rand()+rand()-1.5)*120,27,363);
        y=clamp(c.y+(rand()+rand()+rand()-1.5)*200,24,596);
      } while (++tries<22 && spores.some(s=>(s.x-x)**2+(s.y-y)**2<350));
      const type=typeAt(level,rand);
      const a=rand()*Math.PI*2;
      const v=7+rand()*13+Math.min(level,15)*0.4;
      spores.push({id:i,x,y,vx:Math.cos(a)*v,vy:Math.sin(a)*v,
        type,r: type==='violet'?12:type==='gold'?11:10,
        angle:rand()*Math.PI*2,phase:rand()*6.28,alive:true,popAt:0});
    }
    const shots=Math.max(2,5-Math.floor((level-1)/5));
    const target=Math.ceil(count*(level>=8?.75:level>=4?.68:.58));
    return {count,shots,target,spores};
  }
  function radiusFor(type) {
    switch(type){case 'rose':return 99;case 'azure':return 78;
      case 'gold':return 132;case 'violet':return 72;default:return 86;}
  }
  function scoreFor(type,chain){
    const base=type==='gold'?180:type==='violet'?150:type==='rose'?115:100;
    return base*Math.min(12,1+Math.floor((Math.max(1,chain)-1)/2));
  }
  function inside(px,py,x,y,r){return (px-x)**2+(py-y)**2<=r*r;}
  function move(spore,dt, w=390, h=620){
    const next={...spore};
    if(!next.alive)return next;
    next.x+=next.vx*dt;next.y+=next.vy*dt;
    if(next.x<next.r){next.x=next.r;next.vx=Math.abs(next.vx);}
    if(next.x>w-next.r){next.x=w-next.r;next.vx=-Math.abs(next.vx);}
    if(next.y<next.r){next.y=next.r;next.vy=Math.abs(next.vy);}
    if(next.y>h-next.r){next.y=h-next.r;next.vy=-Math.abs(next.vy);}
    return next;
  }
  return {rng,makeLevel,radiusFor,scoreFor,inside,move,clamp,COLORS,TYPES};
});
