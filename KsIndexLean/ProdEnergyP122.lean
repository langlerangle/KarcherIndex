module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P122: window [-384,-321] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP122 : Finset ℤ := Finset.Ioc (-385) (-321)
theorem eP122_c : tableEnergyNumerator t wP122 1 0 = (220084087504010566103700730369147500426603630350569380910396519308961513331007888583981640341930707 : ℤ) := by decide +kernel
theorem eP122_r : tableEnergyRadius t wP122 1 0 = (1778018787786737677136008942999703807713953637056787311602851106898933581181365762022355461 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
