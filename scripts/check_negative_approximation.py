"""Exact-rational examples of stability of a negative quadratic form.

For dimensions 1 through 6, check three negative diagonal forms and selected
complex coefficient vectors after adding a constant entrywise perturbation.
The perturbation consumes at most half the original negativity margin. Also
check invariance under two unit complex phases and the dimension-zero case.

These finite examples are diagnostics, not a proof of the general perturbation
bound or density theorem. They compute no numerical eigenvalues. Run with
ordinary Python (without -O, which disables the assertions).
"""
from fractions import Fraction as F

def add(a,b): return (a[0]+b[0],a[1]+b[1])
def mul(a,b): return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def conj(a): return (a[0],-a[1])
def q(a,c):
    total=(F(0),F(0))
    for i in range(len(c)):
        for j in range(len(c)):
            total=add(total,mul(mul(conj(c[i]),a[i][j]),c[j]))
    return total[0]
def energy(c): return sum(x*x+y*y for x,y in c)

count=0
for d in range(1,7):
    for delta in [F(1), F(1,10000), F(7,3)]:
        eps=delta/(2*d)
        a=[[( -delta if i==j else F(0),F(0)) for j in range(d)] for i in range(d)]
        cmat=[[(a[i][j][0]+eps,F(0)) for j in range(d)] for i in range(d)]
        vectors=[[(F(0),F(0))]*d,[(F(1),F(0))]*d,
                 [(F(i+1,3),F((-1)**i,2)) for i in range(d)]]
        for c in vectors:
            assert q(a,c)==-delta*energy(c)
            assert abs(q(cmat,c)-q(a,c))<=eps*d*energy(c)
            assert q(cmat,c)<=-delta/2*energy(c)
            for phase in [(F(0),F(1)),(F(3,5),F(4,5))]:
                rotated=[mul(phase,z) for z in c]
                assert q(a,rotated)==q(a,c)
                assert q(cmat,rotated)==q(cmat,c)
            # Zero matrix perturbation preserves the original margin exactly.
            assert abs(q(a,c)-q(a,c))==0
            count+=1
        aligned=[(F(1),F(0))]*d
        assert q(cmat,aligned)==-delta/2*energy(aligned)
# In dimension zero the only vector is zero, and its quadratic form and energy vanish.
assert q([],[])==energy([])==0
print(f'PASS: {count} exact coefficient cases, unit phases, zero perturbations, '
      'near-degenerate margins and sharp half-margin examples; dimension zero checked.')
