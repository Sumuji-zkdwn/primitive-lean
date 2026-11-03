"""Exact singular F16 Moore-Penrose certificates, independently checked."""
from fractions import Fraction as Q
import json
import check_f16_spectral as F

def check():
    eps=F.signed_table(); P=F.zmat(); Qm=F.zmat()
    for j in range(16):
        P[3^j][j]=eps[3][j]
        Qm[10^j][j]=eps[10][j]
    I=F.ident(); D=F.zmat(); K=F.zmat()
    for i in [4,5,6,7,12,13,14,15]:D[i][i]=1
    for i,j,v in [(4,13,-2),(13,4,-2),(7,14,-2),(14,7,-2),
                  (5,12,2),(12,5,2),(6,15,2),(15,6,2)]:K[i][j]=v
    plus=F.add(F.smul(Q(1,2),D),F.smul(Q(1,4),K))
    minus=F.sub(F.smul(Q(1,2),D),F.smul(Q(1,4),K))
    zero=F.sub(I,D)
    count=0
    for t,projector in ((1,plus),(-1,minus)):
        L=F.add(P,F.smul(Q(t),Qm))
        H=F.mul(F.transpose(L),L)
        G=F.add(F.smul(Q(1,4),projector),F.smul(Q(1,2),zero))
        assert H==F.add(F.smul(4,projector),F.smul(2,zero))
        assert F.mul(F.mul(H,G),H)==H
        assert F.mul(F.mul(G,H),G)==G
        assert F.transpose(F.mul(H,G))==F.mul(H,G)
        assert F.transpose(F.mul(G,H))==F.mul(G,H)
        assert F.rank(H)==12
        count+=4
    return dict(passed=True,penrose_equations=count,rank_at_both_singular_inputs=12,
                source="actual F16 signed table, exact rational operations")

if __name__=="__main__":
    print(json.dumps(check(),indent=2))
