"""Lean feedback environment, preserving reset/step semantics from PDF pp.8-10.

ARC adapter: curve parameters are replaced by explicit recorded graph nodes.
Action = edge-application tactic, or reflexivity. Every transition in production
is checked by ReachSession; an accepted proof is re-elaborated without sorry.
This environment never sends an action to ARC. No artificial episode step cap:
repeated nodes are pruned because cycles are unnecessary for graph reachability.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import deque
import hashlib,json
import numpy as np

MAX_CHOICES=16 # Existing empirical graph stores at most 16 transitions per context.
FEATURES_PER_EDGE=8
OBS_DIM=6+MAX_CHOICES*FEATURES_PER_EDGE
N_ACTIONS=MAX_CHOICES+1

@dataclass(frozen=True)
class ProofTask:
    edges:tuple[tuple[int,int,int],...]
    start:int
    target:int
    action_payloads:tuple[tuple[int,dict],...]=()
    scope:str='recorded_model'
    goal_kind:str='recorded_progress'
    event_ids:tuple[str,...]=()
    def __post_init__(self):
        if any(len(e)!=3 or any(type(x) is not int or x<0 for x in e) for e in self.edges):
            raise ValueError('invalid edge')
        if type(self.start) is not int or type(self.target) is not int or min(self.start,self.target)<0:
            raise ValueError('invalid endpoint')
        if len(set(self.edges))!=len(self.edges):raise ValueError('duplicate edge')
        degrees={}
        for s,a,t in self.edges:degrees.setdefault(s,0);degrees[s]+=1
        if any(n>MAX_CHOICES for n in degrees.values()):raise ValueError('model outdegree exceeds supported edge slots')
    @property
    def key(self):
        return hashlib.sha256(json.dumps([self.edges,self.start,self.target,self.scope,self.event_ids],sort_keys=True).encode()).hexdigest()
    def distances(self):
        reverse={}
        for s,a,t in self.edges:reverse.setdefault(t,[]).append(s)
        d={self.target:0};q=deque([self.target])
        while q:
            t=q.popleft()
            for s in reverse.get(t,[]):
                if s not in d:d[s]=d[t]+1;q.append(s)
        return d


class LeanProofEnv:
    def __init__(self,session,task:ProofTask):
        self.session=session;self.task=task;self.dist=task.distances();self.ended=True
        self.outgoing={}
        for e in task.edges:self.outgoing.setdefault(e[0],[]).append(e)
        for es in self.outgoing.values():es.sort(key=lambda e:(e[1],e[2]))
        self.nodes={x for e in task.edges for x in (e[0],e[2])}|{task.start,task.target}
    def choices(self):return self.outgoing.get(self.node,[])[:MAX_CHOICES]
    def observation(self):
        n=max(1,len(self.nodes));d=self.dist.get(self.node,n)
        v=[float(self.node==self.task.target),len(self.seen)/n,len(self.path)/n,
           min(d/n,1.0),len(self.choices())/MAX_CHOICES,float(self.task.goal_kind=='recorded_progress')]
        for e in self.choices():
            s,a,t=e;dd=self.dist.get(t,n)
            v += [1.0,float(t==self.task.target),float(t in self.seen),min(dd/n,1.0),
                  np.tanh(a/16),len(self.outgoing.get(t,[]))/MAX_CHOICES,
                  float(dd<d),float(t in self.dist)]
        v += [0.0]*(OBS_DIM-len(v))
        return np.array(v,dtype=np.float32)
    def mask(self):
        mask=np.zeros(N_ACTIONS,dtype=bool)
        if self.node==self.task.target:mask[-1]=True
        else:
            mask[:len(self.choices())]=True
            if not mask.any():mask[-1]=True # Dead end -> explicit failed finish, not success.
        return mask
    def reset(self, *, seed=None,options=None):
        self.node=self.task.start;self.seen={self.node};self.path=[];self.tactics=[];self.ended=False
        r=self.session.start(self.task.edges,self.task.start,self.task.target)
        return self.observation(),{'lean_res':r,'task':self.task.key}
    def step(self,action):
        if self.ended:raise RuntimeError('reset required after proof termination')
        idx=int(action)
        if idx<0 or idx>=N_ACTIONS or not self.mask()[idx]:
            self.ended=True
            return self.observation(),-11.0,True,False,{'success':False,'reason':'invalid_tactic_slot'}
        e=None if idx==MAX_CHOICES else self.choices()[idx]
        status,r=self.session.advance(e)
        if status=='error':
            self.ended=True
            return self.observation(),-11.0,True,False,{'success':False,'reason':'lean_error','lean_res':r}
        if e is not None:self.node=e[2];self.path.append(e)
        if status=='complete':
            # An empty goal is necessary, not sufficient: audited full theorem required.
            cert=self.session.finish();self.ended=True
            return self.observation(),99.0,True,False,{'success':True,'lean_res':r,
                'certificate':cert,'edge_path':list(self.path)}
        if e is None:
            self.ended=True
            return self.observation(),-11.0,True,False,{'success':False,'reason':'unexpected_open_finish','lean_res':r}
        if self.node in self.seen:
            self.ended=True
            return self.observation(),-11.0,True,False,{'success':False,'reason':'cycle_pruned','lean_res':r}
        self.seen.add(self.node)
        return self.observation(),-1.0,False,False,{'success':False,'lean_res':r}
    def close(self):pass # Session belongs to the trainer, not to an episode.
