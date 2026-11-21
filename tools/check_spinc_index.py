"""Exact topological index arithmetic for canonical Spin^c on CP^2.

The spin^c index formula is a mathematical input from Atiyah--Singer; this
program checks the arithmetic, not the topology of CP^2 or a Standard Model.
"""
import sympy as s

k=s.symbols('k',integer=True)
c1=2*k+3
index=s.factor((c1*c1-1)/8)
assert s.expand(index-(k+1)*(k+2)/2)==0
assert index.subs(k,0)==1  # canonical Spin^c, L=O(3)
assert index.subs(k,-1)==0 # L=O(1)
assert index.subs(k,1)==3  # twist by O(1), L=O(5)
for n in range(-100,101):
    ind=index.subs(k,n)
    assert ind.is_Integer
print('PASS: CP2 Spin^c index = (k+1)(k+2)/2; canonical k=0 gives index 1')
print('INPUT theorem: index = (c1(L)^2 - signature(CP2))/8, signature=1')
