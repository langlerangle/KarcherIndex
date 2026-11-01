module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P57: window [-4544,-4481] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP57 : Finset ℤ := Finset.Ioc (-4545) (-4481)
theorem eP57_c : tableEnergyNumerator t wP57 1 0 = (1436263889292969760103705243891637563216300107340761454052646945959264467972513601760208372569484 : ℤ) := by decide +kernel
theorem eP57_r : tableEnergyRadius t wP57 1 0 = (11749731409005359032658301099475097168595402117065461004522667267629081534661371010029457 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
