"use strict";
/*
 * THEOREM ARCADE finite rule ports.
 *
 * Mathematical source:
 * - LinearInputRule481.rule / step (3x3 torus), reflect_ns, step_two_cycle
 * - LinearInputLaaksoSigned.liftGraph, middleParity, connectedness examples
 * - ClockAvalancheExample.stabilize, observation, balanced_example
 *
 * JavaScript execution is NOT the Lean kernel; tests replay concrete witnesses
 * and check finite exhaustive instances where tractable.
 */
(function(root,make) {
  const api=make();
  if(typeof module!=="undefined" && module.exports) module.exports=api;
  root.TheoremArcade=api;
})(globalThis, function() {
  const SOURCES=Object.freeze({
    rule481:"linear_input/lean_check/Rule481Symmetry.inc",
    laakso:"linear_input/lean_check/LaaksoSignedConnection.inc",
    sandpile:"experiments/sandpile_laakso/formalization/ClockAvalancheExample.lean"
  });
  function rule481(c,n,e,s,w) {
    const score=(c?1:0)+2*((n?1:0)+(e?1:0)+(s?1:0)+(w?1:0));
    return [0,5,6,7,8].includes(score)?1:0;
  }
  const wrap=(a,n)=>((a%n)+n)%n;
  function caInitial(n=17) {
    if(!Number.isInteger(n)||n<3||n>41) throw Error("CA size is 3..41");
    return {size:n, board:Array(n*n).fill(0),ticks:0};
  }
  function caFlip(s,x,y) {
    const n=s.size, b=s.board.slice(),i=wrap(y,n)*n+wrap(x,n);
    b[i]^=1;
    return {...s,board:b};
  }
  function caStep(s) {
    const n=s.size, b=s.board;
    const at=(x,y)=>b[wrap(y,n)*n+wrap(x,n)];
    const next=b.map((_,i)=>{
      const x=i%n,y=Math.floor(i/n);
      return rule481(at(x,y),at(x,y-1),at(x+1,y),at(x,y+1),at(x-1,y));
    });
    return {size:n,board:next,ticks:s.ticks+1};
  }
  function caReflectNS(s) {
    const n=s.size;
    return {...s,board:s.board.map((_,i)=>s.board[wrap(-Math.floor(i/n),n)*n+i%n])};
  }
  function caComplement(s) {
    return {...s,board:s.board.map(v=>1-v)};
  }
  function caFill(s,kind="random",seed=1) {
    const n=s.size;
    let x=seed>>>0;
    const draw=()=>{x^=x<<13;x^=x>>>17;x^=x<<5;return x>>>0;};
    const board=s.board.map((_,i)=>{
      const row=Math.floor(i/n),col=i%n;
      if(kind==="blank")return 0;
      if(kind==="all")return 1;
      if(kind==="cross")return row===Math.floor(n/2)||col===Math.floor(n/2)?1:0;
      if(kind==="mirror")return (draw()&1);
      return (draw()%5===0)?1:0;
    });
    if(kind==="mirror"){
      for(let row=0;row<n;row++)if(row>0 && row>n-row)for(let col=0;col<n;col++)
        board[row*n+col]=board[wrap(-row,n)*n+col];
    }
    return {...s,board};
  }
  function caPopulation(s){return s.board.reduce((a,v)=>a+v,0);}

  // First Laakso approximant; two central parallel edges are NOT merged.
  const LA_EDGES=Object.freeze([[0,4],[1,4],[4,5],[4,5],[5,2],[5,3]]);
  function laInitial(signature=[0,0,0,1,0,0]) {
    if(signature.length!==6 || signature.some(x=>x!==0&&x!==1))throw Error("six bits expected");
    return {signature:signature.slice(), actions:0, repairs:0};
  }
  function laParity(s){return s.signature[2]^s.signature[3];}
  function laToggle(s,e) {
    if(!Number.isInteger(e)||e<0||e>=6)throw Error("edge id 0..5");
    const signature=s.signature.slice();signature[e]^=1;
    return {...s,signature,repairs:s.repairs+1};
  }
  function laSwitch(s,v) {
    if(!Number.isInteger(v)||v<0||v>=6)throw Error("vertex id 0..5");
    const signature=s.signature.map((bit,i)=>{
      const [a,b]=LA_EDGES[i];
      return bit^Number(v===a)^Number(v===b);
    });
    return {...s,signature,actions:s.actions+1};
  }
  function laLift(s) {
    const edges=[];
    s.signature.forEach((bit,i)=>{
      const [a,b]=LA_EDGES[i];
      for(let layer=0;layer<2;layer++)
        edges.push([2*a+layer,2*b+(layer^bit),i]);
    });
    return edges;
  }
  function laReachable(s,start=8) {
    if(!Number.isInteger(start)||start<0||start>=12)throw Error("lift vertex out of range");
    const neighbors=Array.from({length:12},()=>[]);
    for(const [a,b] of laLift(s)){neighbors[a].push(b);neighbors[b].push(a);}
    const visited=new Set([start]),queue=[start];
    for(let i=0;i<queue.length;i++)for(const nb of neighbors[queue[i]])
      if(!visited.has(nb)){visited.add(nb);queue.push(nb);}
    return [...visited].sort((a,b)=>a-b);
  }
  function laCompatibleSpin(s) {
    // Satisfies the actual Lean Compatible definition on the base graph.
    for(let mask=0;mask<64;mask++){
      if(LA_EDGES.every(([a,b],i)=>(((mask>>a)&1)^((mask>>b)&1))===s.signature[i]))
        return Array.from({length:6},(_,v)=>(mask>>v)&1);
    }
    return null;
  }
  function laCycle(s) {
    return [8,10,8+laParity(s)]; // Base vertex 4 at sheet 0 -> vertex 5 -> vertex 4 in sheet parity
  }

  const SAND_ROWS=Object.freeze([
    [3,1,3,1,1,3,2,1],[1,3,1,0,2,1,3,2],
    [3,1,1,3,3,1,1,3],[1,2,3,3,3,3,2,1],
    [3,3,3,3,3,3,3,3],[3,3,3,3,3,3,3,3],
    [3,3,3,3,3,3,3,3],[3,3,3,3,3,3,3,3]
  ]);
  function sandInitial() {
    const first=SAND_ROWS.flat();
    const second=SAND_ROWS.flatMap(row=>row.slice().reverse());
    return {a:first,b:second,topA:0,topB:0,round:0,seen:[],lastA:[],lastB:[],failed:null};
  }
  function sandField(i,j,q) {
    return Number(i+j>q&&i+q>j&&j+q>i&&i+j+q<18&&(i+j+q)%2===1);
  }
  const SHORT=Array.from({length:64},(_,k)=>
    Array.from({length:8},(_,j)=>(j+1)%3===0?sandField(Math.floor(k/8)+1,k%8+1,j+1):0)
      .reduce((a,b)=>a+b,0)%2);
  const LONG=Array.from({length:64},(_,k)=>
    Array.from({length:8},(_,j)=>(j+1)%3!==0?sandField(Math.floor(k/8)+1,k%8+1,j+1):0)
      .reduce((a,b)=>a+b,0)%2);
  function sandObserve(board) {
    const weighted=board.reduce((sum,v,k)=>sum+v*(Math.floor(k/8)+1)*(k%8+1),0);
    const bit=(weights)=>board.reduce((sum,v,k)=>sum+v*weights[k],0)%2;
    return [(5*weighted)%9,bit(SHORT),bit(LONG)];
  }
  function sandStabilize(before,site) {
    if(!Number.isInteger(site)||site<0||site>=64)throw Error("site 0..63");
    const board=before.slice();board[site]++;
    let count=0,seen=new Set(),round=0;
    for(;round<64;round++){
      const active=[];
      for(let k=0;k<64;k++)if(board[k]>=4)active.push(k);
      if(active.length===0) return {board,count,fired:[...seen].sort((a,b)=>a-b),rounds:round};
      // A round fires each currently unstable site once, simultaneously.
      const next=board.slice();
      for(const k of active) {
        next[k]-=4; count++;seen.add(k);
        const x=k%8,y=Math.floor(k/8);
        if(y>0)next[k-8]++;
        if(y<7)next[k+8]++;
        if(x>0)next[k-1]++;
        if(x<7)next[k+1]++;
      }
      board.splice(0,board.length,...next);
    }
    // The source's option is none when fuel expires on an unstable board.
    if(board.some(v=>v>=4))return null;
    return {board,count,fired:[...seen].sort((a,b)=>a-b),rounds:round};
  }
  function sandDrive(s,site=0,grains=2) {
    if(s.failed) return s;
    if(!Number.isInteger(grains)||grains<1||grains>2)throw Error("one or two grains");
    let a=s.a,b=s.b,addedA=0,addedB=0,lastA=[],lastB=[];
    for(let j=0;j<grains;j++) {
      const x=sandStabilize(a,site),y=sandStabilize(b,site);
      if(x===null||y===null)return {...s,failed:"64-round stabilization budget expired"};
      a=x.board;b=y.board;
      addedA+=x.count;addedB+=y.count;
      lastA=x.fired;lastB=y.fired;
      if(sandObserve(a).join(",")!==sandObserve(b).join(","))
        return {...s,failed:"the observations unexpectedly diverged"};
    }
    return {...s,a,b,topA:s.topA+addedA,topB:s.topB+addedB,
      round:s.round+1,seen:s.seen.concat([[site,grains,addedA,addedB]]),
      lastA,lastB};
  }
  function sandWitness(n=81) {
    if(!Number.isInteger(n)||n<0||n>81)throw Error("witness prefix is 0..81");
    let s=sandInitial();
    for(let i=0;i<n;i++)s=sandDrive(s,i%2===0?0:7,2);
    return s;
  }
  return Object.freeze({SOURCES,rule481,caInitial,caFlip,caStep,caReflectNS,caComplement,caFill,caPopulation,
    LA_EDGES,laInitial,laParity,laToggle,laSwitch,laLift,laReachable,laCompatibleSpin,laCycle,
    SAND_ROWS,sandInitial,sandField,sandObserve,sandStabilize,sandDrive,sandWitness});
});
