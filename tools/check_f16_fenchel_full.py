"""Independent exact-rational sanity check for the actual F16 16x16 left pencil.

No floating-point eigensolver, and no replacement for kernel-checked Lean.
"""
from fractions import Fraction as Q
from pathlib import Path
import re
import json

ROOT = Path(__file__).resolve().parents[1]
SIGN_FILE = ROOT / "linear_input/lean_check/F16Holonomy.inc"

def signs():
    txt = SIGN_FILE.read_text("utf-8")
    m = re.search(r"def epsTable\s*:\s*Array \(Array ℤ\)\s*:=\s*#\[([\s\S]*?)\]\s*\n\ndef eps", txt)
    assert m, "F16 signed table missing"
    rows = re.findall(r"#\[([\d,\s-]+)\]", m.group(1))
    eps = [list(map(int, row.split(","))) for row in rows]
    assert len(eps) == 16 and all(len(row) == 16 for row in eps)
    return eps

def mat(t, eps):
    out = [[Q(0) for _ in range(16)] for _ in range(16)]
    for j in range(16):
        out[3 ^ j][j] += Q(eps[3][j])
        out[10 ^ j][j] += Q(t * eps[10][j])
    return out

def transpose(a):
    return [list(row) for row in zip(*a)]

def mul(a, b):
    return [[sum((x*y for x,y in zip(row,col)), Q(0)) for col in transpose(b)] for row in a]

def mv(a, v):
    return [sum((x*y for x,y in zip(row,v)), Q(0)) for row in a]

def rank(a):
    x = [row.copy() for row in a]; m=len(x); n=len(x[0]); pivot=0
    for col in range(n):
        i=next((i for i in range(pivot,m) if x[i][col]), None)
        if i is None: continue
        x[pivot],x[i]=x[i],x[pivot]
        div=x[pivot][col];x[pivot]=[v/div for v in x[pivot]]
        for j in range(m):
            if j!=pivot and x[j][col]:
                d=x[j][col];x[j]=[v-d*w for v,w in zip(x[j],x[pivot])]
        pivot+=1
        if pivot==m:break
    return pivot

def dot(x,y):
    return sum((a*b for a,b in zip(x,y)),Q(0))

def check():
    eps=signs()
    tested=0
    for t in [-2,-1,0,1,2]:
        a=mat(t,eps); gram=mul(transpose(a),a)
        expected=12 if abs(t)==1 else 16
        assert rank(a)==rank(gram)==expected
        xs=[[Q((i+j)%5-2) for i in range(16)] for j in range(3)]
        for x in xs:
            p=mv(gram,x)
            for y in xs:
                diff=[v-u for u,v in zip(x,y)]
                score_x=dot(p,x)-dot(mv(a,x),mv(a,x))/2
                score_y=dot(p,y)-dot(mv(a,y),mv(a,y))/2
                assert score_x-score_y==dot(mv(a,diff),mv(a,diff))/2
                tested+=1
        if abs(t)==1:
            assert any(rank([*gram,[Q(int(i==j)) for i in range(16)]])>rank(gram) for j in range(16))
    return dict(passed=True,rank={"regular":16,"t=+1":12,"t=-1":12},
                sharp_dual_checks=tested,scope="full 16D rational matrix, exact discrete sample")

if __name__ == "__main__":
    print(json.dumps(check(),indent=2))
