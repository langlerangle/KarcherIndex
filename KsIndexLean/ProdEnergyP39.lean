module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP31

@[expose] public section

/-! Energy chunk P39: window [-5696,-5633] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP39 : Finset ℤ := Finset.Ioc (-5697) (-5633)
theorem eP39_c : tableEnergyNumerator t wP39 1 0 = (920117559105638660062785774408525243988764015191330956407506713357299169132943281039219476138855 : ℤ) := by decide +kernel
theorem eP39_r : tableEnergyRadius t wP39 1 0 = (7534967796021734714654041201138516016799698782426002038835060216235738903097020123658543 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
