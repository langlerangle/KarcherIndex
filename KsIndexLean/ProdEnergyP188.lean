module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP180

@[expose] public section

/-! Energy chunk P188: window [3840,3903] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP188 : Finset ℤ := Finset.Ioc (3839) (3903)
theorem eP188_c : tableEnergyNumerator t wP188 1 0 = (164482639883685049706499781730338087691208486168693711629155397982734737816139232733615702007096 : ℤ) := by decide +kernel
theorem eP188_r : tableEnergyRadius t wP188 1 0 = (4617407774066000774521788191654517167425272979754590318570197044038068763320576687472782 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
