module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P7: window [-7744,-7681] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP7 : Finset ℤ := Finset.Ioc (-7745) (-7681)
theorem eP7_c : tableEnergyNumerator t wP7 1 0 = (503083203194558860500890691619398728813096684828320490684863026097491723633591680375133433542009 : ℤ) := by decide +kernel
theorem eP7_r : tableEnergyRadius t wP7 1 0 = (4125460188056160296493078848795843233259646670533167266168824139699712429955932106074693 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
