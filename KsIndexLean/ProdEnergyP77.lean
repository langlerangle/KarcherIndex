module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP69

@[expose] public section

/-! Energy chunk P77: window [-3264,-3201] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP77 : Finset ℤ := Finset.Ioc (-3265) (-3201)
theorem eP77_c : tableEnergyNumerator t wP77 1 0 = (2762667944659871443055245298790450923522642188645000840888197711490717686655504360672295000178702 : ℤ) := by decide +kernel
theorem eP77_r : tableEnergyRadius t wP77 1 0 = (22566301811124377920801341027120125376925684866164810213887244638485568349699947764038782 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
