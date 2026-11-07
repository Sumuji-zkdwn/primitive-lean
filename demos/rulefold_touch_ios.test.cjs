'use strict';
const {test}=require('node:test');
const assert=require('node:assert/strict');
const fs=require('node:fs');
const path=require('node:path');
const vm=require('node:vm');
const html=fs.readFileSync(path.join(__dirname,'RULEFOLD_TOUCH_iOS.html'),'utf8');
const scripts=[...html.matchAll(/<script(?:[^>]*)>([\s\S]*?)<\/script>/g)].map(x=>x[1]);
test('inline JS parses without missing modules',()=>{
  assert.equal(scripts.length,5);
  scripts.forEach(code=>assert.doesNotThrow(()=>new vm.Script(code)));
});
test('mobile viewport and safe areas',()=>{
  assert.match(html,/viewport-fit=cover/);
  assert.doesNotMatch(html,/user-scalable=no/);
  assert.match(html,/safe-area-inset-bottom/);
  assert.match(html,/--ios-fh/);
});
test('touch fallback and original controls survive',()=>{
  for(const id of ['easyTiles','easyGrow','easyUndo','easySave','rfPanel','world','gif','mp4','png'])
    assert.ok(html.includes('id="'+id+'"'));
  assert.match(html,/if\(!window\.PointerEvent\)/);
  assert.match(html,/try\{canvas\.setPointerCapture/);
});
function fakeBridge(ua,platform='iPhone',touches=5){
  const nodes=new Map(),calls=[];
  const elem=id=>{
    if(!nodes.has(id))nodes.set(id,{hidden:true,textContent:'',handlers:{},
      addEventListener(event,fn){this.handlers[event]=fn},removeAttribute(k){delete this[k]}});
    return nodes.get(id);
  };
  const sandbox={window:{},document:{getElementById:elem},
    navigator:{userAgent:ua,platform,maxTouchPoints:touches,canShare:()=>true,share:async data=>calls.push(data)},
    Blob,File:class {constructor(data,name,opts){this.name=name;this.type=opts.type}},
    URL:{createObjectURL:()=> 'blob:test',revokeObjectURL(){}}
  };
  vm.runInNewContext(scripts.at(-1),sandbox);
  return {bridge:sandbox.window.IOSBridge,elem,calls};
}
test('iPhone and iPadOS Safari desktop mode detected',()=>{
  assert.equal(fakeBridge('iPhone').bridge.isIOS,true);
  assert.equal(fakeBridge('Macintosh','MacIntel',5).bridge.isIOS,true);
  assert.equal(fakeBridge('Macintosh','MacIntel',0).bridge.isIOS,false);
});
test('generated file uses a deliberate Share action',async()=>{
  const ui=fakeBridge('iPhone');
  ui.bridge.present(new Blob(['GIF89a'],{type:'image/gif'}),'test.gif');
  assert.equal(ui.elem('iosSaveSheet').hidden,false);
  assert.equal(ui.elem('iosDownload').download,'test.gif');
  await ui.elem('iosShare').handlers.click();
  assert.equal(ui.calls.length,1);
  assert.equal(ui.calls[0].files[0].name,'test.gif');
  ui.bridge.close();
  assert.equal(ui.elem('iosSaveSheet').hidden,true);
});
test('bounded local restoration, mobile render cap, MP4 fallback',()=>{
  assert.match(html,/rulefold-touch-ios-v1/);
  assert.match(html,/snap\.history=\[\]/);
  assert.match(html,/240000/);
  assert.match(html,/GIFで作成する/);
  assert.match(html,/MP4録画がタイムアウト/);
});
