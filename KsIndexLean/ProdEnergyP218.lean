module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P218: window [5760,5823] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP218 : Finset ℤ := Finset.Ioc (5759) (5823)
theorem eP218_c : tableEnergyNumerator t wP218 1 0 = (87952638278261697342804153897602868673891570909836299956607909932197074418754210212650581365054 : ℤ) := by decide +kernel
theorem eP218_r : tableEnergyRadius t wP218 1 0 = (2279896060702741375336328683285472871574966456307182373498879719030490289426054994968598 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
