module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P132: window [256,319] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP132 : Finset ℤ := Finset.Ioc (255) (319)
theorem eP132_c : tableEnergyNumerator t wP132 1 0 = (4988111312969711200304925916245140387946169275532432771808013203923116632427971870237708541715364 : ℤ) := by decide +kernel
theorem eP132_r : tableEnergyRadius t wP132 1 0 = (327931112210268530982501978493503919521417167816231389589209390643109219065561105748942017 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
