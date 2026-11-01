module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P166: window [2432,2495] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP166 : Finset ℤ := Finset.Ioc (2431) (2495)
theorem eP166_c : tableEnergyNumerator t wP166 1 0 = (325766290854171686706041644395880439978278641348004619624537458730087794423605284808332114784546 : ℤ) := by decide +kernel
theorem eP166_r : tableEnergyRadius t wP166 1 0 = (10105740244106847198354487724152854101405243315875136360865916398625545341862916251590675 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
