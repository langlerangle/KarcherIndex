module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP15

@[expose] public section

/-! Energy chunk P23: window [-6720,-6657] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP23 : Finset ℤ := Finset.Ioc (-6721) (-6657)
theorem eP23_c : tableEnergyNumerator t wP23 1 0 = (664696608617150278095659831808314845998834955512160035485928683425259841518211102595073419158980 : ℤ) := by decide +kernel
theorem eP23_r : tableEnergyRadius t wP23 1 0 = (5447319887650050477057923411134345944629102964274400590359735558315206758335036794855684 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
