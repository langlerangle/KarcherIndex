module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P113: window [-960,-897] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP113 : Finset ℤ := Finset.Ioc (-961) (-897)
theorem eP113_c : tableEnergyNumerator t wP113 1 0 = (32191852632242149149224069001527792554148923558450511455172328061179854697258699761338068471512990 : ℤ) := by decide +kernel
theorem eP113_r : tableEnergyRadius t wP113 1 0 = (261388195394675423702730645521997070323440166693777127040995844154713862327988553108007062 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
