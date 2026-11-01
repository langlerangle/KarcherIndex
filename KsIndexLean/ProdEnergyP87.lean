module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P87: window [-2624,-2561] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP87 : Finset ℤ := Finset.Ioc (-2625) (-2561)
theorem eP87_c : tableEnergyNumerator t wP87 1 0 = (4260473089994059775596775137688608968154620852460472835322812626457487328702297587781642318048519 : ℤ) := by decide +kernel
theorem eP87_r : tableEnergyRadius t wP87 1 0 = (34765222089005824194210623648653026200532863094921074331775209874032126114015211397001774 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
