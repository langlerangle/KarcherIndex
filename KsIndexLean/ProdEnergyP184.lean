module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP176

@[expose] public section

/-! Energy chunk P184: window [3584,3647] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP184 : Finset ℤ := Finset.Ioc (3583) (3647)
theorem eP184_c : tableEnergyNumerator t wP184 1 0 = (182660348060864199728728031784849752996966380928267454532451516451572109083428886329428387170065 : ℤ) := by decide +kernel
theorem eP184_r : tableEnergyRadius t wP184 1 0 = (5201858804216022291779938750124791299009266649334766542326382968487899069683503493824032 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
