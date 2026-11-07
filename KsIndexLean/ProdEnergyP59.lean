module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP51

@[expose] public section

/-! Energy chunk P59: window [-4416,-4353] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP59 : Finset ℤ := Finset.Ioc (-4417) (-4353)
theorem eP59_c : tableEnergyNumerator t wP59 1 0 = (1519579871307170941990699279137260106737486424824027866102391328402508444077850342822013320093416 : ℤ) := by decide +kernel
theorem eP59_r : tableEnergyRadius t wP59 1 0 = (12429698593518177240172384079821770359725049261094818984363827157514179886680978255227855 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
