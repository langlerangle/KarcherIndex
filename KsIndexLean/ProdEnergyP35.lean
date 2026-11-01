module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P35: window [-5952,-5889] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP35 : Finset ℤ := Finset.Ioc (-5953) (-5889)
theorem eP35_c : tableEnergyNumerator t wP35 1 0 = (843856068109044723386056634260016714602609102943508649955510723284907936651962616256269602306231 : ℤ) := by decide +kernel
theorem eP35_r : tableEnergyRadius t wP35 1 0 = (6911816808438010814916681964664543376063816484231515462113657611415401539896806504720951 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
