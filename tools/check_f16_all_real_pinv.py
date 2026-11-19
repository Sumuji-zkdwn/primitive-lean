"""Exact-rational regression for all-real F16 spectral Moore-Penrose formulas.

Finite rational probes independently use the original signed epsilon table.
Not a substitute for the Lean all-real theorem or its axiom audit.
"""
from fractions import Fraction as Q
import json
import check_f16_spectral as F

def check():
    eps=F.signed_table(); L3=F.zmat(); L10=F.zmat()
    for j in range(16):
        L3[3^j][j]=eps[3][j]
        L10[10^j][j]=eps[10][j]
    I=F.ident(); D=F.zmat(); K=F.zmat(); zeros=F.zmat()
    for i in (4,5,6,7,12,13,14,15): D[i][i]=1
    for i,j,v in ((4,13,-2),(13,4,-2),(7,14,-2),(14,7,-2),
                  (5,12,2),(12,5,2),(6,15,2),(15,6,2)): K[i][j]=v
    Pp=F.add(F.smul(Q(1,2),D),F.smul(Q(1,4),K))
    Pm=F.sub(F.smul(Q(1,2),D),F.smul(Q(1,4),K))
    Pz=F.sub(I,D)
    def diag(t):
        return F.add(F.add(F.smul((t+1)**2,Pp),
                           F.smul((t-1)**2,Pm)),F.smul(1+t*t,Pz))
    def scalar_inv0(x):return Q(0) if x==0 else 1/x
    def general(t):
        return F.add(F.add(F.smul(scalar_inv0((t+1)**2),Pp),
                           F.smul(scalar_inv0((t-1)**2),Pm)),
                     F.smul(scalar_inv0(1+t*t),Pz))
    def penrose(A,B):
        return [F.mul(F.mul(A,B),A)==A,F.mul(F.mul(B,A),B)==B,
                F.transpose(F.mul(A,B))==F.mul(A,B),
                F.transpose(F.mul(B,A))==F.mul(B,A)]
    tested=[Q(-3),Q(-2),Q(-1),Q(-1,2),Q(0),Q(1,2),Q(1),Q(2),Q(3)]
    result=[]
    for t in tested:
        A=F.add(L3,F.smul(t,L10)); N=F.mul(F.transpose(A),A); G=general(t)
        assert N==diag(t)
        assert all(penrose(N,G)),("Gram Penrose",t)
        Aplus=F.mul(G,F.transpose(A))
        assert all(penrose(A,Aplus)),("Left Penrose",t)
        assert F.rank(A)==(12 if abs(t)==1 else 16)
        assert F.rank(N)==(12 if abs(t)==1 else 16)
        if t not in (-1,1):
            assert F.mul(N,G)==I and F.mul(G,N)==I
        z=[[Q(i+1)] for i in range(16)]
        p=F.mul(N,z)
        Np=F.mul(G,p)
        v=F.mul(F.transpose(F.mul(A,z)),F.mul(A,z))[0][0]/2
        dual=F.mul(F.transpose(p),Np)[0][0]/2
        assert v==dual,("Fenchel finite value",t)
        result.append(str(t))
    assert general(Q(1))==F.add(F.smul(Q(1,4),Pp),F.smul(Q(1,2),Pz))
    assert general(Q(-1))==F.add(F.smul(Q(1,4),Pm),F.smul(Q(1,2),Pz))
    assert scalar_inv0(Q(1,100)**2)>1000
    return dict(passed=True,tested_parameters=result,
                gram_penrose_checks=4*len(tested),
                left_penrose_checks=4*len(tested),
                finite_dual_exact_checks=len(tested),
                real_all_parameter_formula_proved_in_python=False)

if __name__=="__main__":
    print(json.dumps(check(),indent=2))
