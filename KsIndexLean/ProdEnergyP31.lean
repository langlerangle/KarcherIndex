module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P31: window [-6208,-6145] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP31 : Finset ℤ := Finset.Ioc (-6209) (-6145)
theorem eP31_c : tableEnergyNumerator t wP31 1 0 = (776767289187562656322199187672795473033113248546174714624909911257266365594489465554224171736698 : ℤ) := by decide +kernel
theorem eP31_r : tableEnergyRadius t wP31 1 0 = (6363509636136987433380662306399736123485932264869706281811086750878565566246975178050461 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
