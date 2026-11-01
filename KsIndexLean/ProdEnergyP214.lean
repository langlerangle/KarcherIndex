module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P214: window [5504,5567] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP214 : Finset ℤ := Finset.Ioc (5503) (5567)
theorem eP214_c : tableEnergyNumerator t wP214 1 0 = (94422574034762349594825504552868135162597014539162773541167758764657211457263804757245831528774 : ℤ) := by decide +kernel
theorem eP214_r : tableEnergyRadius t wP214 1 0 = (2468645227231583666329031624268365103122400278776322506048369413403850556623318649544667 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
