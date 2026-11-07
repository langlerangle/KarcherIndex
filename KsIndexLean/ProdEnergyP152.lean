module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP144

@[expose] public section

/-! Energy chunk P152: window [1536,1599] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP152 : Finset ℤ := Finset.Ioc (1535) (1599)
theorem eP152_c : tableEnergyNumerator t wP152 1 0 = (629148847228230780386599785943438946590766162638115467558079949653792453061199513658959579206650 : ℤ) := by decide +kernel
theorem eP152_r : tableEnergyRadius t wP152 1 0 = (21861567692567490021252556916480966434685427315539873830889182985872360502646967132163941 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
