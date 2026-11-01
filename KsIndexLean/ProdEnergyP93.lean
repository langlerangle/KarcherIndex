module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P93: window [-2240,-2177] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP93 : Finset ℤ := Finset.Ioc (-2241) (-2177)
theorem eP93_c : tableEnergyNumerator t wP93 1 0 = (5838097645489975141272209698867932457370916229760540588462271298107974538443694347430650873426781 : ℤ) := by decide +kernel
theorem eP93_r : tableEnergyRadius t wP93 1 0 = (47602755429356708047114756207056462848050468935609443870315945021450710288131621193136835 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
