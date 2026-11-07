module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP113

@[expose] public section

/-! Energy chunk P121: window [-448,-385] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP121 : Finset ℤ := Finset.Ioc (-449) (-385)
theorem eP121_c : tableEnergyNumerator t wP121 1 0 = (157768185892590490593889230321764151426006253131710979806458980197010422138896590827649359010920339 : ℤ) := by decide +kernel
theorem eP121_r : tableEnergyRadius t wP121 1 0 = (1275738913252252809746423648580763560660508386595613501593947529412342411535060439955694616 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
