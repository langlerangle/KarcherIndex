module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P144: window [1024,1087] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP144 : Finset ℤ := Finset.Ioc (1023) (1087)
theorem eP144_c : tableEnergyNumerator t wP144 1 0 = (1089993445778961182181176581902817039390569005768229814879643361583536690167495873099840283656239 : ℤ) := by decide +kernel
theorem eP144_r : tableEnergyRadius t wP144 1 0 = (42412581000620978115797762873648149640354430172361811035776358416728414006382757908028500 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
