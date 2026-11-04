'use strict';
const {test}=require('node:test');
const assert=require('node:assert/strict');
const fs=require('node:fs');
const path=require('node:path');
const vm=require('node:vm');
const html=fs.readFileSync(path.join(__dirname,'rulefold_mandala.html'),'utf8');
const code=html.match(/<script id="rulefold-core">([\s\S]*?)<\/script>/)?.[1];
assert.ok(code);
const E=vm.runInNewContext(code+'\nRulefoldCore;');
const plain=x=>JSON.parse(JSON.stringify(x));

test('PR73: Fin4 mutable path is 0,1,2,3',()=>{
  const r=E.run(E.seed(true),n=>n<4);
  assert.equal(r.saturated,true);
  assert.deepEqual(plain(r.history.map(h=>h.state.known)),[[0],[0,1],[0,1,2],[0,1,2,3]]);
  assert.deepEqual(plain(r.state.edges),[[0,1],[1,2],[2,3]]);
  assert.equal(E.classes(r.state),4);
});
test('PR73: frozen control stalls with 3 operators',()=>{
  const r=E.run(E.seed(false),n=>n<4);
  assert.equal(r.saturated,true);
  assert.deepEqual(plain(r.state.known),[0,1,2]);
  assert.equal(E.classes(r.state),3);
});
test('New lift emits next meta but current edge uses old meta',()=>{
  const s=E.seed(true),a=E.step(s),b=E.step(a.state);
  assert.deepEqual(plain(a.event.edges),[[1,2]]);
  assert.deepEqual(plain(a.event.installed),[{on:1,meta:{on:2,from:2,to:3}}]);
  assert.deepEqual(plain(a.event.emitted),[{on:2,from:2,to:3}]);
  assert.deepEqual(plain(b.event.edges),[[2,3]]);
  assert.equal(s.liftRules.length,0);
});
test('Machine-state visual signature is deterministic and changes on transition',()=>{
  const s=E.seed(true),a=E.visual(s),b=E.visual(E.step(s).state);
  assert.deepEqual(plain(E.visual(s)),plain(a));
  assert.notEqual(a.seed,b.seed);
  assert.ok(a.duty>=.15&&a.duty<=.75);
  assert.ok(['xor','majority'].includes(b.combine));
});
test('External graft after saturation opens a finite new frontier',()=>{
  const s=E.run(E.seed(true),n=>n<4).state;
  const g=E.graft(s,24);
  assert.deepEqual(plain(E.frontier(g)),[4]);
  const next=E.step(g,n=>n<24);
  assert.deepEqual(plain(next.state.known),[0,1,2,3,4]);
  assert.deepEqual(plain(next.event.edges),[[4,5]]);
});
test('Finite lab reaches 24 only with repeated explicit external graft',()=>{
  let s=E.seed(true),grafts=0,steps=0;
  while(s.known.length<24 && steps<100){
    const a=E.step(s,n=>n<24);
    if(a){s=a.state;steps++;}else{s=E.graft(s,24);assert.ok(s);grafts++;}
  }
  assert.equal(s.known.length,24);assert.equal(steps,23);
  assert.ok(grafts>0);assert.equal(E.graft(s,24),null);
});
test('Operator E M L D injection changes respective tables',()=>{
  const s=E.seed(true),v={on:2,from:3,to:4};
  assert.deepEqual(plain(E.attach(s,'edge',v).edges.at(-1)),[3,4]);
  assert.deepEqual(plain(E.attach(s,'meta',v).metaRules.at(-1)),v);
  assert.deepEqual(plain(E.attach(s,'lift',v).liftRules.at(-1)),{on:2,meta:{on:3,from:3,to:4}});
  assert.deepEqual(plain(E.attach(s,'edit',v).liftEdits.at(-1)),{on:2,rule:{on:2,meta:{on:3,from:3,to:4}}});
});
test('Malformed or out-of-catalogue programs cannot be imported',()=>{
  const s=E.seed(true);
  assert.deepEqual(plain(E.validate(s)),plain(s));
  assert.throws(()=>E.validate({...s,known:[0,24]}));
  assert.throws(()=>E.validate({...s,edges:[[0,'bad']]}));
  assert.throws(()=>E.attach(s,'edge',{on:0,from:2,to:24}));
});
test('Original mandala export controls and touch behavior are retained',()=>{
  for(const id of ['world','more','gif','mp4','png','stateSave','stateLoad','loadInput'])
    assert.ok(html.includes('id="'+id+'"'));
  for(const word of ['createGIFEncoder','oneGif(','oneMp4(','onePng(','pointerDown(','pointerUp(','design:\'continuous-3-phase-binary\''])
    assert.ok(html.includes(word),word);
});
test('Rulefold panel is optional and locally runnable',()=>{
  assert.match(html,/<aside id="rfPanel" hidden/);
  for(const id of ['rfLaunch','rfNext','rfRun','rfGraft','rfInsert','rfGif','rfExport','rfImport'])
    assert.ok(html.includes('id="'+id+'"'));
  assert.match(html,/option value="studio" selected/);
});
