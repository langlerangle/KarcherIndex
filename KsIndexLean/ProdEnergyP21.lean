module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P21: window [-6848,-6785] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP21 : Finset ℤ := Finset.Ioc (-6849) (-6785)
theorem eP21_c : tableEnergyNumerator t wP21 1 0 = (640500818767471161374747781627658282489808800481707568838899740549946194726307304906309701723684 : ℤ) := by decide +kernel
theorem eP21_r : tableEnergyRadius t wP21 1 0 = (5249471462737250936332615811658025247023774355933085873461874195205445121793460860141054 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
