module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P172: window [2816,2879] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP172 : Finset ℤ := Finset.Ioc (2815) (2879)
theorem eP172_c : tableEnergyNumerator t wP172 1 0 = (262348805395731693591138793302851907495721927040366982861063610615662972194514671725043945325060 : ℤ) := by decide +kernel
theorem eP172_r : tableEnergyRadius t wP172 1 0 = (7871545529454106544152905083244371262783135733264590105603643940109694983842722129933799 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
