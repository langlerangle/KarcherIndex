module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP37

@[expose] public section

/-! Energy chunk P45: window [-5312,-5249] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP45 : Finset ℤ := Finset.Ioc (-5313) (-5249)
theorem eP45_c : tableEnergyNumerator t wP45 1 0 = (1055676671108368474982260690075832301131888312938889863519500742203666014039292928608567016984836 : ℤ) := by decide +kernel
theorem eP45_r : tableEnergyRadius t wP45 1 0 = (8642360711813742314459528257941566691670088842827927801470598470983072420191651925119270 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
