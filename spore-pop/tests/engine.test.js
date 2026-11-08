const assert=require('node:assert/strict');
const R=require('../Web/engine.js');
const a=R.makeLevel(5), b=R.makeLevel(5);
assert.deepEqual(a,b,'deterministic waves');
assert.equal(R.makeLevel(1).count,18);
assert.equal(R.makeLevel(1).shots,5);
assert.equal(R.makeLevel(8).shots,4);
for(let lv=1;lv<=25;lv++){
 const x=R.makeLevel(lv);
 assert.equal(x.spores.length,x.count);
 assert.ok(x.target>0&&x.target<=x.count);
 for(const s of x.spores){
   assert.ok(s.x>=s.r&&s.x<=390-s.r);
   assert.ok(s.y>=s.r&&s.y<=620-s.r);
   assert.ok(R.radiusFor(s.type)>s.r);
 }
}
assert.equal(R.radiusFor('gold'),132);
assert.equal(R.scoreFor('lumen',1),100);
assert.equal(R.scoreFor('lumen',5),300);
assert.equal(R.scoreFor('lumen',999),1200);
assert.ok(R.inside(3,4,0,0,5));
assert.ok(!R.inside(6,0,0,0,5));
const m=R.move({x:11,y:10,vx:-10,vy:0,r:10,alive:true},1);
assert.equal(m.x,10);assert.equal(m.vx,10);
console.log('PASS: SPORE POP game rules: seeded waves, caps, collision, score, bounce');
