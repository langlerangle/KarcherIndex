module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P248: window [7680,7743] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP248 : Finset ℤ := Finset.Ioc (7679) (7743)
theorem eP248_c : tableEnergyNumerator t wP248 1 0 = (55894906769254891568271257337243058877862690427734029951412958990969844100400648426368558290252 : ℤ) := by decide +kernel
theorem eP248_r : tableEnergyRadius t wP248 1 0 = (1375316831417214134649289105082923613030994903304767819451142151247018367867385908407438 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
