module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP112

@[expose] public section

/-! Energy chunk P120: window [-512,-449] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP120 : Finset ℤ := Finset.Ioc (-513) (-449)
theorem eP120_c : tableEnergyNumerator t wP120 1 0 = (118708393014501898192387374187020390277832459045861400471411212794012012578530182965025042231478752 : ℤ) := by decide +kernel
theorem eP120_r : tableEnergyRadius t wP120 1 0 = (960627939150797168122752061797416673945571920446408944552321449278997261925297709252334924 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
