module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP121

@[expose] public section

/-! Energy chunk P129: window [64,127] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP129 : Finset ℤ := Finset.Ioc (63) (127)
theorem eP129_c : tableEnergyNumerator t wP129 1 0 = (6539285330864166941931933124031463429270076674211699664296952173280338191902301552338825851775262 : ℤ) := by decide +kernel
theorem eP129_r : tableEnergyRadius t wP129 1 0 = (1123898404949174907245809963521776657575652013770487534563547656312809205615999699222572937 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
