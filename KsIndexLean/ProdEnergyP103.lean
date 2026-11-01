module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P103: window [-1600,-1537] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP103 : Finset ℤ := Finset.Ioc (-1601) (-1537)
theorem eP103_c : tableEnergyNumerator t wP103 1 0 = (11446456563575767381270742511545758812365373582236832140783479573762712660617477921500823481855337 : ℤ) := by decide +kernel
theorem eP103_r : tableEnergyRadius t wP103 1 0 = (93180431554222823830140749354252791170985607528879704621242877058594012348847922415603735 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
