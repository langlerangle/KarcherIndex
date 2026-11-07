module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP35

@[expose] public section

/-! Energy chunk P43: window [-5440,-5377] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP43 : Finset ℤ := Finset.Ioc (-5441) (-5377)
theorem eP43_c : tableEnergyNumerator t wP43 1 0 = (1007311780647703321138455786191160396168607474841375923956466923583800315157634057360253997894111 : ℤ) := by decide +kernel
theorem eP43_r : tableEnergyRadius t wP43 1 0 = (8247304865009887181232332930322700613698373211981656770620122391267952923626851940724665 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
