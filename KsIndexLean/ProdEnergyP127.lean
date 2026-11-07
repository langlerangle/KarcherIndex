module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP119

@[expose] public section

/-! Energy chunk P127: window [-64,-1] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP127 : Finset ℤ := Finset.Ioc (-65) (-1)
theorem eP127_c : tableEnergyNumerator t wP127 1 0 = (1063450948501318285649200415831025453462119485718272272395439084389857053915323371394634514099909510151 : ℤ) := by decide +kernel
theorem eP127_r : tableEnergyRadius t wP127 1 0 = (11986315073216273820266346332761582655699594679774511366036046322153373660715937197595334892353 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
