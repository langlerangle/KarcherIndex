module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P170: window [2688,2751] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP170 : Finset ℤ := Finset.Ioc (2687) (2751)
theorem eP170_c : tableEnergyNumerator t wP170 1 0 = (281092699230765474898973571668360180810404905021748670450465650538860104218100190608993119273694 : ℤ) := by decide +kernel
theorem eP170_r : tableEnergyRadius t wP170 1 0 = (8522477090138819049244061796537860988872257199625777859886156798705864345573124451134179 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
