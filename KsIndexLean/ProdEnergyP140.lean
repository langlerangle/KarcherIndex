module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P140: window [768,831] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP140 : Finset ℤ := Finset.Ioc (767) (831)
theorem eP140_c : tableEnergyNumerator t wP140 1 0 = (1574451419629869740940101306332182064852681014444902992370169552468333865710738381228761935037291 : ℤ) := by decide +kernel
theorem eP140_r : tableEnergyRadius t wP140 1 0 = (66977629861493936785900933090784606093873744253677322461631205959175697003032275527146790 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
