module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP71

@[expose] public section

/-! Energy chunk P79: window [-3136,-3073] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP79 : Finset ℤ := Finset.Ioc (-3137) (-3073)
theorem eP79_c : tableEnergyNumerator t wP79 1 0 = (2990648519176222276838645078214942415807280219534684959253618603094931467800094865663190571197219 : ℤ) := by decide +kernel
theorem eP79_r : tableEnergyRadius t wP79 1 0 = (24423960046428092037422951184823444367937578012633333287923073103224299108603523297470568 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
