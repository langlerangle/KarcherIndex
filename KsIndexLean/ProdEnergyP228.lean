module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP220

@[expose] public section

/-! Energy chunk P228: window [6400,6463] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP228 : Finset ℤ := Finset.Ioc (6399) (6463)
theorem eP228_c : tableEnergyNumerator t wP228 1 0 = (74558752527069363618598019739903934513056995577350834465063945901543879947875053414015413907526 : ℤ) := by decide +kernel
theorem eP228_r : tableEnergyRadius t wP228 1 0 = (1895400196612347474047542557690416872316489962076743522895783926194785399957885421932072 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
