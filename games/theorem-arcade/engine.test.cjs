"use strict";
const {test}=require("node:test");
const assert=require("node:assert/strict");
const fs=require("node:fs");
const path=require("node:path");
const E=require("./engine.js");
const root=path.resolve(__dirname,"../..");

test("every rule481 local input agrees with weighted bit definition, complement and reflections",()=>{
  for(let m=0;m<32;m++) {
    const [c,n,e,s,w]=Array.from({length:5},(_,i)=>(m>>i)&1);
    const score=c+2*(n+e+s+w);
    assert.equal(E.rule481(c,n,e,s,w),[0,5,6,7,8].includes(score)?1:0);
    assert.equal(E.rule481(c,n,e,s,w),E.rule481(c,n,w,s,e));
    assert.equal(E.rule481(c,n,e,s,w),E.rule481(c,s,e,n,w));
    assert.equal(E.rule481(1-c,1-n,1-e,1-s,1-w),1-E.rule481(c,n,e,s,w));
  }
});

test("Rule 481 two-cycle and spatial mirror theorem hold on entire 3x3 state space",()=>{
  for(let bits=0;bits<512;bits++){
    const s={size:3,ticks:0,board:Array.from({length:9},(_,i)=>(bits>>i)&1)};
    assert.deepEqual(E.caStep(E.caReflectNS(s)).board,E.caReflectNS(E.caStep(s)).board);
    assert.deepEqual(E.caStep(E.caComplement(s)).board,E.caComplement(E.caStep(s)).board);
  }
  assert.deepEqual(E.caStep(E.caInitial(3)).board,Array(9).fill(1));
  assert.deepEqual(E.caStep(E.caStep(E.caInitial(3))).board,Array(9).fill(0));
});

test("Laakso six named edges form two duplicated middle bridges",()=>{
  assert.deepEqual(E.LA_EDGES,[[0,4],[1,4],[4,5],[4,5],[5,2],[5,3]]);
  assert.equal(E.laLift(E.laInitial()).length,12);
});

test("all 64 Laakso edge signatures have reachability class determined by middle parity",()=>{
  for(let mask=0;mask<64;mask++){
    const signature=Array.from({length:6},(_,i)=>(mask>>i)&1);
    const s=E.laInitial(signature),parity=E.laParity(s);
    for(let layer=0;layer<2;layer++)
      assert.equal(E.laReachable(s,8+layer).length,parity===0?6:12);
    assert.equal(E.laCompatibleSpin(s)!==null,parity===0);
    for(let v=0;v<6;v++){
      const switched=E.laSwitch(s,v);
      assert.equal(E.laParity(switched),parity,"vertex gauge switch cannot change middle parity");
      assert.equal(E.laReachable(switched,8).length,E.laReachable(s,8).length);
    }
    const after=E.laToggle(s,3);
    assert.equal(E.laParity(after),parity^1);
    assert.notEqual(E.laReachable(after,8).length,E.laReachable(s,8).length);
  }
});

test("square sandpile initial boards have 158 grains each and identical observations",()=>{
  const s=E.sandInitial();
  assert.equal(s.a.reduce((a,b)=>a+b,0),158);
  assert.equal(s.b.reduce((a,b)=>a+b,0),158);
  assert.deepEqual(E.sandObserve(s.a),[0,0,0]);
  assert.deepEqual(E.sandObserve(s.b),[0,0,0]);
});

test("the Lean balanced_example witness replays exactly, with all intermediate readings equal",()=>{
  let s=E.sandInitial();
  for(let i=0;i<81;i++){
    s=E.sandDrive(s,i%2===0?0:7,2);
    assert.equal(s.failed,null);
    assert.deepEqual(E.sandObserve(s.a),E.sandObserve(s.b));
    assert.ok(s.a.every(v=>v>=0&&v<4) && s.b.every(v=>v>=0&&v<4));
    if(i===79){
      assert.equal(s.topA,95);
      assert.equal(s.topB,95);
    }
  }
  assert.equal(s.topA,95);
  assert.equal(s.topB,158);
  assert.deepEqual(E.sandWitness(81),s);
});

test("other symmetric-input sandpile drives preserve the three-element observation",()=>{
  let s=E.sandInitial();
  for(let i=0;i<18;i++){
    const site=(i*17)%64;
    s=E.sandDrive(s,site,i%2?1:2);
    assert.equal(s.failed,null);
    assert.deepEqual(E.sandObserve(s.a),E.sandObserve(s.b));
  }
});

test("read-only provenance references exist with actual Lean declarations",()=>{
  const proofs=[
    [E.SOURCES.rule481,["def rule (","theorem step_mirror","theorem step_two_cycle"]],
    [E.SOURCES.laakso,["def liftGraph","theorem untwisted_reachable_card","theorem flipped_reachable_card","theorem flipped_no_spin"]],
    [E.SOURCES.sandpile,["def observation","def stabilize","theorem balanced_example : replay = some (95, 95, 95, 158)"]]
  ];
  for(const [name,declarations] of proofs){
    const src=fs.readFileSync(path.join(root,name),"utf8");
    for(const declaration of declarations)assert.ok(src.includes(declaration),name+" missing "+declaration);
  }
});
