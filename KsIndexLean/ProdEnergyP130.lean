module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP122

@[expose] public section

/-! Energy chunk P130: window [128,191] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP130 : Finset ℤ := Finset.Ioc (127) (191)
theorem eP130_c : tableEnergyNumerator t wP130 1 0 = (7374312164229006008062909545585913656877208924036169127088577535783099356994015700560863450655350 : ℤ) := by decide +kernel
theorem eP130_r : tableEnergyRadius t wP130 1 0 = (721122432419677961510857295624694149341632717370012360461636601817743044043980909847792053 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
