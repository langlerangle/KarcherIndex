module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P49: window [-5056,-4993] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP49 : Finset ℤ := Finset.Ioc (-5057) (-4993)
theorem eP49_c : tableEnergyNumerator t wP49 1 0 = (1163579962315519730717515553446498880876303904281710715505923434854655007115736949989911357102079 : ℤ) := by decide +kernel
theorem eP49_r : tableEnergyRadius t wP49 1 0 = (9523589533937654966117531837775145942046033676759882293229255672517816496629192539931909 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
