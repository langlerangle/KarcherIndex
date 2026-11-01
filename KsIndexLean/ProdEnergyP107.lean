module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P107: window [-1344,-1281] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP107 : Finset ℤ := Finset.Ioc (-1345) (-1281)
theorem eP107_c : tableEnergyNumerator t wP107 1 0 = (16260546618048149280258950320705636493303826753108407066505776410596174321691307092825369955503696 : ℤ) := by decide +kernel
theorem eP107_r : tableEnergyRadius t wP107 1 0 = (132255791558723205720010212888814581295909942650627879452016058988968940920994321108627263 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
