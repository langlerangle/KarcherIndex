#!/usr/bin/env python3
"""Generate exact rational multiplier certificates for the alpha-star tail bound.

Uses only the Python standard library. Supply --output to select the Lean file
to write; this script is not run by the default project build.
"""

import argparse
from fractions import Fraction as F
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="destination for AlphaGroupMultiplierCert.lean")
    output = parser.parse_args().output

    # Inputs are the shifts and integer coefficient numerators in
    # AlphaRemarkTrial.lean and AlphaTrialIntegerData.lean.
    # Combine each exponent/parity group before bounding it, preserving
    # cancellation. Translate x = 2051 + y and compare polynomial coefficients
    # to obtain bounds valid for every y >= 0. Lean checks the emitted data;
    # separate identity theorems connect these functions to the trial multipliers.
    shift = [6,5,4,3,2,1,-1,-2,-3,-4,-5,-6, 6,5,4,3,2,1,0,-1,-2,-3,-4,-5,-6]
    coeffNum = [678297074,-3847817393,10105953973,-12255602695,-15903023220,237044154676,
        -237044154676,15903023220,12255602695,-10105953973,3847817393,-678297074,
        -2064148267,15584704300,-60384017740,157391608797,-309175124422,546623219487,
        347930602765,546623219487,-309175124422,157391608797,-60384017740,15584704300,-2064148267]
    bA, bB = F(4323618,10**7), F(5676382,10**7)

    def add(a,b): return [(a[i] if i<len(a) else F(0))+(b[i] if i<len(b) else F(0)) for i in range(max(len(a),len(b)))]
    def mul(a,b):
        o=[F(0)]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b): o[i+j]+=x*y
        return o
    def product(ps):
        o=[F(1)]
        for p in ps: o=mul(o,p)
        return o
    def translate(p,x0):  # coeffs of p(x0+y) in y
        from math import comb as C
        return [sum(p[j]*C(j,i)*x0**(j-i) for j in range(i,len(p))) for i in range(len(p))]
    def value(p,x):
        a=F(0)
        for v in reversed(p): a=a*x+v
        return a

    def group(beta,lo,hi,parity):
        terms=[(shift[i],F(coeffNum[i],10**12)) for i in range(lo,hi) if shift[i]%2==parity]
        base=min(j for j,_ in terms); degree=(max(j for j,_ in terms)-base)//2
        den=[[beta+base+2*l+2,F(1)] for l in range(degree)]
        num=[[beta-base-2*l,F(-1)] for l in range(degree)]
        numerator=[F(0)]
        for sh,c in terms:
            k=(sh-base)//2
            numerator=add(numerator,[c*v for v in product(num[:k]+den[k:])])
        return base,numerator,product(den),terms

    def direct_ratio(beta,base,terms,x):
        tot=F(0)
        for sh,c in terms:
            r=F(1)
            for l in range((sh-base)//2): r*=(beta-(x+base+2*l))/(beta+x+base+2*l+2)
            tot+=c*r
        return tot

    fams=[('A',bA,0,12),('B',bB,12,25)]
    EXACT=[]
    print("cutoff fam par base   multiplier [L, U]                         cap            id_ok bnd_ok")
    for cutoff in (64,256,1024,8192):
        x0=2*cutoff+3
        for name,beta,lo,hi in fams:
            for par in (0,1):
                base,p,q,terms=group(beta,lo,hi,par)
                pp,qq=translate(p,x0),translate(q,x0)
                qpos=all(v>0 for v in qq)
                ratios=[u/v for u,v in zip(pp,qq)]
                L,U=min(ratios),max(ratios)
                bnd_ok = qpos and all(L*v<=u<=U*v for u,v in zip(pp,qq))  # the RationalCoefficientComparison hyp
                # identity + in-range check at several x>=x0 (exact)
                id_ok=True
                for x in (x0,x0+1,2*x0,100*x0,10**6):
                    mv=value(p,x)/value(q,x)
                    if mv!=direct_ratio(beta,base,terms,x) or not (L<=mv<=U): id_ok=False
                cap=max(abs(L),abs(U))
                print(f"{cutoff:5d}  {name}  {par}  {base:3d}  [{float(L): .8g},{float(U): .8g}]  {float(cap):.8g}   {id_ok}  {bnd_ok}")
                if cutoff==1024:
                    EXACT.append((name,par,base,L,U,len(pp)-1))

    # print the exact ℚ bounds for the Lean statements
    print("\n=== EXACT certified ℚ bounds at cutoff 1024 (x0=2051), for the Lean multiplier cert ===")
    for name,par,base,L,U,deg in EXACT:
        print(f"  {name} par{par} base{base} deg{deg}:  L = {L.numerator}/{L.denominator}")
        print(f"                        U = {U.numerator}/{U.denominator}   (~[{float(L):.10g},{float(U):.10g}])")

    # ---- Lean-ready integer data + outward-bound validation (x >= x0 = 2051 ⇔ y = x-2051 >= 0) ----
    print("\n=== LEAN DATA (x0=2051): integer num/den coeffs + validated outward [L,U] ===")
    from math import gcd
    def clear_pair(pp,qq):   # clear num & den by ONE common denominator so the ratio is preserved
        D=1
        for f in pp+qq: D=D*f.denominator//gcd(D,f.denominator)
        return [int(f*D) for f in pp],[int(f*D) for f in qq]
    outward={('A',0):(F(0),F(1,10000)),('A',1):(F(-491,1000),F(-489,1000)),
             ('B',0):(F(-85,100),F(-845,1000)),('B',1):(F(0),F(3,10000))}
    x0=2051
    LEAN=[]
    for name,beta,lo,hi in fams:
        for par in (0,1):
            base,p,q,terms=group(beta,lo,hi,par)
            pp,qq=translate(p,x0),translate(q,x0)
            P,Q=clear_pair(pp,qq)
            L,U=outward[(name,par)]
            assert all(d>0 for d in Q), (name,par)   # rational_integer_coefficients_bound needs d_i>0
            lo_ok=all(L.numerator*d<=L.denominator*pi for pi,d in zip(P,Q))   # L.num*d ≤ L.den*p
            hi_ok=all(U.denominator*pi<=U.numerator*d for pi,d in zip(P,Q))   # U.den*p ≤ U.num*d
            assert lo_ok and hi_ok, (name,par,lo_ok,hi_ok)
            print(f"  {name} par{par} base{base}:  L={L}  U={U}  [validated integer coeffwise ✓]")
            print(f"     p (num) = {P}")
            print(f"     d (den) = {Q}")
            LEAN.append((name,par,base,L,U,P,Q))

    def arr(xs): return "![" + ", ".join(str(v) for v in xs) + "]"
    out=["module", "", "public import KsIndexLean.RationalCoefficientComparison", "",
     "@[expose] public section", "", "",
     "/-! Generated integer coefficient certificates for four rational functions.",
     "",
     "Each exponent/parity group has numerator and denominator coefficient vectors in",
     "`y = x - 2051`, together with rational bounds `[L, U]`. The theorems below prove",
     "the coefficient inequalities in Lean and apply",
     "`rational_integer_coefficients_bound` for `y ≥ 0`. Identification of these",
     "rational functions with the trial multipliers is supplied separately.",
     "-/","","namespace KsIndex.AlphaMultiplier",""]
    for name,par,base,L,U,P,Q in LEAN:
        tag=f"{name}{par}"; n=len(P)
        out+=[f"-- family {name} parity {par} base {base}: multiplier bound [{L}, {U}]  (degree {n-1})",
              f"def p_{tag} : Fin {n} → ℤ := {arr(P)}",
              f"def d_{tag} : Fin {n} → ℤ := {arr(Q)}",
              f"def L_{tag} : ℚ := {L.numerator}/{L.denominator}",
              f"def U_{tag} : ℚ := {U.numerator}/{U.denominator}",
              f"/-- Multiplier `{name}` parity `{par}` (base {base}): for y = x - 2051 ≥ 0 (x ≥ 2051),",
              f"    the rational function (Σ pᵢ yⁱ)/(Σ dᵢ yⁱ) lies in [L_{tag}, U_{tag}]. -/",
              f"theorem mult_bound_{tag} (y : ℝ) (hy : 0 ≤ y) :",
              f"    (L_{tag} : ℝ) ≤ (∑ i, (p_{tag} i : ℝ) * y ^ i.val) / (∑ i, (d_{tag} i : ℝ) * y ^ i.val) ∧",
              f"      (∑ i, (p_{tag} i : ℝ) * y ^ i.val) / (∑ i, (d_{tag} i : ℝ) * y ^ i.val) ≤ (U_{tag} : ℝ) :=",
              f"  rational_integer_coefficients_bound {n} p_{tag} d_{tag} L_{tag} U_{tag} y hy",
              f"    (by decide) (by decide)",
              f"    (by intro i; fin_cases i <;> norm_num [p_{tag}, d_{tag}, L_{tag}, U_{tag}])",
              f"    (by intro i; fin_cases i <;> norm_num [p_{tag}, d_{tag}, L_{tag}, U_{tag}])",""]
    out.append("end KsIndex.AlphaMultiplier")
    output.write_text("\n".join(out)+"\n", encoding="utf-8")
    print(f"\nWrote {output} (four group certificates and bounds theorems).")


if __name__ == "__main__":
    main()
