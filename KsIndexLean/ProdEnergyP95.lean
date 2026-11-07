module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP87

@[expose] public section

/-! Energy chunk P95: window [-2112,-2049] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP95 : Finset ℤ := Finset.Ioc (-2113) (-2049)
theorem eP95_c : tableEnergyNumerator t wP95 1 0 = (6565273552606782308656447648873164028410179244521997801668223783825250823440885361205380484339795 : ℤ) := by decide +kernel
theorem eP95_r : tableEnergyRadius t wP95 1 0 = (53516933167866762310074457266588063132776384924962016294918038841027056081820736267393260 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
