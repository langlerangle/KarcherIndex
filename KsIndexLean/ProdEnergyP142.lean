module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP134

@[expose] public section

/-! Energy chunk P142: window [896,959] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP142 : Finset ℤ := Finset.Ioc (895) (959)
theorem eP142_c : tableEnergyNumerator t wP142 1 0 = (1296160895394531824453839882485093439176634051424685632698591043641333836874803027756561633723426 : ℤ) := by decide +kernel
theorem eP142_r : tableEnergyRadius t wP142 1 0 = (52513590541944480592667902262393076539550466670062866177106785000392543791388912733003338 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
