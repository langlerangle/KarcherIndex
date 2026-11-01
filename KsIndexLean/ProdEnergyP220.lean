module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P220: window [5888,5951] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP220 : Finset ℤ := Finset.Ioc (5887) (5951)
theorem eP220_c : tableEnergyNumerator t wP220 1 0 = (84979939461520154849318825960151021300083304631766359464357816784603601428276359551042214876263 : ℤ) := by decide +kernel
theorem eP220_r : tableEnergyRadius t wP220 1 0 = (2193814269343849665311215118899702516406968014655018324519829486276503883631540535533384 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
