module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP7

@[expose] public section

/-! Energy chunk P15: window [-7232,-7169] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP15 : Finset ℤ := Finset.Ioc (-7233) (-7169)
theorem eP15_c : tableEnergyNumerator t wP15 1 0 = (575400266805397767979830028966325498042045321274642673410976967588038510822312151895297626453187 : ℤ) := by decide +kernel
theorem eP15_r : tableEnergyRadius t wP15 1 0 = (4717057647087480767509587950332034694092495872474860775672374233503839532952951394696128 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
