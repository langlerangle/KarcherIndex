module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP83

@[expose] public section

/-! Energy chunk P91: window [-2368,-2305] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP91 : Finset ℤ := Finset.Ioc (-2369) (-2305)
theorem eP91_c : tableEnergyNumerator t wP91 1 0 = (5226084894143996728466695963278487228727249745239534092109348627652632397803027032937360564576336 : ℤ) := by decide +kernel
theorem eP91_r : tableEnergyRadius t wP91 1 0 = (42623809772416449430529297042246318877513251027772213289394047709082481635041843401282479 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
