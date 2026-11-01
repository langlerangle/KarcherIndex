module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P119: window [-576,-513] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP119 : Finset ℤ := Finset.Ioc (-577) (-513)
theorem eP119_c : tableEnergyNumerator t wP119 1 0 = (92600579994876798279470732906175180210680862588557231946782335249665378378526439504203396175269154 : ℤ) := by decide +kernel
theorem eP119_r : tableEnergyRadius t wP119 1 0 = (749847534053789741192632957926572131818413182076928920054374337258821722523720961775937281 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
