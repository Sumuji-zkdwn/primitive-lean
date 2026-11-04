// No dependency besides Node.js. Run: node --test demos/higher_order_playground.test.cjs
'use strict';
const {test}=require('node:test');
const assert=require('node:assert/strict');
const fs=require('node:fs');
const path=require('node:path');
const vm=require('node:vm');
const html=fs.readFileSync(path.join(__dirname,'higher_order_playground.html'),'utf8');
const source=html.match(/<script id="rulefold-engine">([\s\S]*?)<\/script>/)?.[1];
assert.ok(source,'Engine script must remain inline for offline standalone HTML');
const E=vm.runInNewContext(source+'\nRulefoldEngine');
const plain=value=>JSON.parse(JSON.stringify(value));

const allowed=()=>true;

test('PR #73: mutable machine learns 0,1,2,3 and saturates',()=>{
  const r=E.run(E.state(true),allowed);
  assert.deepEqual(plain(r.history.map(x=>x.state.known)),[[0],[0,1],[0,1,2],[0,1,2,3]]);
  assert.equal(r.saturated,true);
  assert.deepEqual(plain(r.state.edges),[[0,1],[1,2],[2,3]]);
  assert.equal(E.observationClasses(r.state),4);
});

test('PR #73: frozen control stalls at 0,1,2',()=>{
  const r=E.run(E.state(false),allowed);
  assert.deepEqual(plain(r.history.map(x=>x.state.known)),[[0],[0,1],[0,1,2]]);
  assert.equal(r.saturated,true);
  assert.deepEqual(plain(r.state.edges),[[0,1],[1,2]]);
  assert.equal(E.observationClasses(r.state),3);
});

test('Newly installed lift emits meta, but old meta alone generates current edges',()=>{
  const initial=E.state(true),first=E.step(initial,allowed);
  assert.deepEqual(plain(first.event.addedEdges),[[1,2]]);
  assert.deepEqual(plain(first.event.installedLiftRules),[{on:1,meta:{on:2,from:2,to:3}}]);
  assert.deepEqual(plain(first.event.emittedMetaRules),[{on:2,from:2,to:3}]);
  assert.deepEqual(plain(first.state.edges),[[0,1],[1,2]]);
  assert.deepEqual(plain(E.step(first.state,allowed).state.edges),[[0,1],[1,2],[2,3]]);
  assert.deepEqual(plain(initial.metaRules),[{on:1,from:1,to:2}]); // pure, immutable updates
  assert.equal(initial.liftRules.length,0);
});

test('If operator 1 is not viable, neither machine can expand',()=>{
  for(const x of [true,false]){
    assert.equal(E.step(E.state(x),n=>n!==1),null);
    assert.deepEqual(plain(E.run(E.state(x),n=>n!==1).state.known),[0]);
  }
});

test('If operator 2 is not viable, both stop at [0,1]',()=>{
  for(const x of [true,false]){
    assert.deepEqual(plain(E.run(E.state(x),n=>n!==2).state.known),[0,1]);
  }
});

test('If operator 3 is not viable, mutable machine stops at [0,1,2]',()=>{
  assert.deepEqual(plain(E.run(E.state(true),n=>n!==3).state.known),[0,1,2]);
});

test('Observations use the exact known-operator child-list readout',()=>{
  const mutable=E.run(E.state(true),allowed).state;
  assert.deepEqual(plain(E.observedBehaviors(mutable)),[[1],[2],[3],[]]);
  const frozen=E.run(E.state(false),allowed).state;
  assert.deepEqual(plain(E.observedBehaviors(frozen)),[[1],[2],[]]);
});

test('All four operators are bounded Fin4 references, no invented states',()=>{
  for(const m of [E.state(true),E.state(false)]){
    const r=E.run(m,allowed);
    assert.ok(r.state.known.every(n=>Number.isInteger(n)&&n>=0&&n<4));
    assert.equal(E.step(r.state,allowed),null);
  }
});
