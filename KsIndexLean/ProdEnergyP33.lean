module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P33: window [-6080,-6017] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP33 : Finset ℤ := Finset.Ioc (-6081) (-6017)
theorem eP33_c : tableEnergyNumerator t wP33 1 0 = (809260763071635600593158028169990537937474127954167659107558944827811463266186876717672241622908 : ℤ) := by decide +kernel
theorem eP33_r : tableEnergyRadius t wP33 1 0 = (6629087487370165869254682028681120426815355580675392539177367902403227667103262386295354 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
