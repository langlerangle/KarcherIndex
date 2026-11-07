module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP135

@[expose] public section

/-! Energy chunk P143: window [960,1023] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP143 : Finset ℤ := Finset.Ioc (959) (1023)
theorem eP143_c : tableEnergyNumerator t wP143 1 0 = (1185809446623051291466017485708538606217934462793519446914485290331681784555912303512900590131155 : ℤ) := by decide +kernel
theorem eP143_r : tableEnergyRadius t wP143 1 0 = (47040677458526658030467691296251084096167307982792682049506869895845810386698919347739521 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
