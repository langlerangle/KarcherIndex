module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P204: window [4864,4927] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP204 : Finset ℤ := Finset.Ioc (4863) (4927)
theorem eP204_c : tableEnergyNumerator t wP204 1 0 = (114412416000058478085812332872081774333814433647975169458976738070702212932276177016424614922826 : ℤ) := by decide +kernel
theorem eP204_r : tableEnergyRadius t wP204 1 0 = (3063128650148533745055949650786844796123230892883382059222877115452584359285809201348304 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
