module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP29

@[expose] public section

/-! Energy chunk P37: window [-5824,-5761] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP37 : Finset ℤ := Finset.Ioc (-5825) (-5761)
theorem eP37_c : tableEnergyNumerator t wP37 1 0 = (880739274089169102031955494010556253311672681604814288887180664905626092236124510204106670820930 : ℤ) := by decide +kernel
theorem eP37_r : tableEnergyRadius t wP37 1 0 = (7213214116858149970829726822449648588242986912494443344498578432210718069048242924262360 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
