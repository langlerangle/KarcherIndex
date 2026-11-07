module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP75

@[expose] public section

/-! Energy chunk P83: window [-2880,-2817] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP83 : Finset ℤ := Finset.Ioc (-2881) (-2817)
theorem eP83_c : tableEnergyNumerator t wP83 1 0 = (3541097289334314741493645644004790920276626292632854223826980072831075145448821526425896761570164 : ℤ) := by decide +kernel
theorem eP83_r : tableEnergyRadius t wP83 1 0 = (28907826185269125247118376964988760697630288906349268260510996872689862927487354640398396 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
