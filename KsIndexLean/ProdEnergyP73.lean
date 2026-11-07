module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP65

@[expose] public section

/-! Energy chunk P73: window [-3520,-3457] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP73 : Finset ℤ := Finset.Ioc (-3521) (-3457)
theorem eP73_c : tableEnergyNumerator t wP73 1 0 = (2378947576117438606133755930410905428716311869874159183374066843806292803774339075962538568955469 : ℤ) := by decide +kernel
theorem eP73_r : tableEnergyRadius t wP73 1 0 = (19438774473519909095827533716746486032115695598879823764226693065707565920689804031071605 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
