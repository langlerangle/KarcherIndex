module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP188

@[expose] public section

/-! Energy chunk P196: window [4352,4415] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP196 : Finset ℤ := Finset.Ioc (4351) (4415)
theorem eP196_c : tableEnergyNumerator t wP196 1 0 = (135819075768896450852854828450877714105005751191251732454403173034812409393630476313457793374426 : ℤ) := by decide +kernel
theorem eP196_r : tableEnergyRadius t wP196 1 0 = (3716996863735442077439689143546419317802098521918879868899684222562745931013294029501852 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
