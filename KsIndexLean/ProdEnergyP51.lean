module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP43

@[expose] public section

/-! Energy chunk P51: window [-4928,-4865] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP51 : Finset ℤ := Finset.Ioc (-4929) (-4865)
theorem eP51_c : tableEnergyNumerator t wP51 1 0 = (1223903378070323970416693212414684598610417650338329425528888249680913037827791621217361634910813 : ℤ) := by decide +kernel
theorem eP51_r : tableEnergyRadius t wP51 1 0 = (10016156024916055559371145568392121017565975674761703118412535658597184828644433470292512 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
