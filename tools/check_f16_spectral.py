"""Exact rational spectral certificate for the original Cayley-Dickson F16."""
from fractions import Fraction as Q
import json, re
from pathlib import Path

BASE=Path(__file__).resolve().parents[1]

def signed_table():
    txt=(BASE/"linear_input/lean_check/F16Holonomy.inc").read_text("utf-8")
    m=re.search(r"def epsTable\s*:\s*Array \(Array ℤ\)\s*:=\s*#\[([\s\S]*?)\]\s*\n\ndef eps",txt)
    assert m
    rows=re.findall(r"#\[([\d,\s-]+)\]",m.group(1))
    a=[list(map(int, r.split(","))) for r in rows]
    assert len(a)==16 and all(len(x)==16 for x in a)
    return a

def zmat():
    return [[Q(0) for _ in range(16)] for _ in range(16)]
def ident():
    a=zmat()
    for i in range(16):a[i][i]=1
    return a
def transpose(a):return [list(col) for col in zip(*a)]
def mul(a,b):
    cols=transpose(b)
    return [[sum((u*v for u,v in zip(row,col)),Q(0)) for col in cols] for row in a]
def smul(c,a):return [[c*x for x in row] for row in a]
def add(a,b):return [[x+y for x,y in zip(row,s)] for row,s in zip(a,b)]
def sub(a,b):return add(a,smul(-1,b))
def rank(a):
    a=[r.copy() for r in a];k=0
    for j in range(16):
        p=next((i for i in range(k,16) if a[i][j]),None)
        if p is None:continue
        a[k],a[p]=a[p],a[k]
        d=a[k][j];a[k]=[x/d for x in a[k]]
        for i in range(16):
            if i!=k and a[i][j]:
                v=a[i][j];a[i]=[x-v*y for x,y in zip(a[i],a[k])]
        k+=1
    return k

def check():
    eps=signed_table()
    p=zmat();q=zmat()
    for j in range(16):
        p[3^j][j]=eps[3][j];q[10^j][j]=eps[10][j]
    I=ident();D=zmat();K=zmat()
    for i in list(range(4,8))+list(range(12,16)):D[i][i]=1
    for i,j,v in [(4,13,-2),(13,4,-2),(7,14,-2),(14,7,-2),
                  (5,12,2),(12,5,2),(6,15,2),(15,6,2)]:K[i][j]=v
    assert mul(transpose(p),p)==I
    assert mul(transpose(q),q)==I
    assert add(mul(transpose(p),q),mul(transpose(q),p))==K
    P=add(smul(Q(1,2),D),smul(Q(1,4),K))
    M=sub(smul(Q(1,2),D),smul(Q(1,4),K))
    Z=sub(I,D)
    assert add(add(P,M),Z)==I
    for A,B,n,v in [(P,M,4,2),(M,Z,4,-2),(Z,P,8,0)]:
        assert mul(A,A)==A
        assert sum((A[i][i] for i in range(16)),Q(0))==n
        assert mul(A,B)==zmat()
        assert transpose(A)==A
        assert mul(K,A)==smul(v,A)
        assert rank(A)==n
    for t in [-2,-1,0,1,2]:
        L=add(p,smul(Q(t),q))
        H=mul(transpose(L),L)
        spectral=add(add(smul((1+t)**2,P),smul((1-t)**2,M)),smul(1+t*t,Z))
        assert H==spectral
        assert rank(H)==(12 if abs(t)==1 else 16)
    return dict(passed=True,projection_ranks=[4,4,8],
                tested_parameters=[-2,-1,0,1,2],
                source="unchanged F16 Cayley-Dickson signed basis table")

if __name__=="__main__":
    print(json.dumps(check(),indent=2))
