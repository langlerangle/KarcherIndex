module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP126

@[expose] public section

/-! Energy chunk P134: window [384,447] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP134 : Finset ℤ := Finset.Ioc (383) (447)
theorem eP134_c : tableEnergyNumerator t wP134 1 0 = (3450515323733625193045434553660073664309058936496064624825254797506692492058756012543085354631899 : ℤ) := by decide +kernel
theorem eP134_r : tableEnergyRadius t wP134 1 0 = (189155438528144309110137357837050239271643948390353819154965391598469520156173849651066933 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
