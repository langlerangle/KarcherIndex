module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP204

@[expose] public section

/-! Energy chunk P212: window [5376,5439] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP212 : Finset ℤ := Finset.Ioc (5375) (5439)
theorem eP212_c : tableEnergyNumerator t wP212 1 0 = (97948776327558686411757764273741972948717370502228308158259283294678763060062149464864262640699 : ℤ) := by decide +kernel
theorem eP212_r : tableEnergyRadius t wP212 1 0 = (2572297237566239000480019190169416653432600974545543358888110557840715563531884872373092 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
