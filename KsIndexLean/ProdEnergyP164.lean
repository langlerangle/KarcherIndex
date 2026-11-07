module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP156

@[expose] public section

/-! Energy chunk P164: window [2304,2367] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP164 : Finset ℤ := Finset.Ioc (2303) (2367)
theorem eP164_c : tableEnergyNumerator t wP164 1 0 = (352583865121604902847404727735686721334966669154922751124357266937103645880082454818185667852695 : ℤ) := by decide +kernel
theorem eP164_r : tableEnergyRadius t wP164 1 0 = (11076621078795568300979713842831894176472585156980229459018820489210683251866732453996191 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
