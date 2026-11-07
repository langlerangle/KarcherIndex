module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP178

@[expose] public section

/-! Energy chunk P186: window [3712,3775] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP186 : Finset ℤ := Finset.Ioc (3711) (3775)
theorem eP186_c : tableEnergyNumerator t wP186 1 0 = (173188230881387925467301937204317212177988435717976887694043476785913716890062119857064380802995 : ℤ) := by decide +kernel
theorem eP186_r : tableEnergyRadius t wP186 1 0 = (4896068784638405704267367059407641666087824911863131421446351736407574185383682427593453 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
