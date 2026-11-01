module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P148: window [1280,1343] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP148 : Finset ℤ := Finset.Ioc (1279) (1343)
theorem eP148_c : tableEnergyNumerator t wP148 1 0 = (808806259469125638854015778312606870125159635044024246396815340959570625259439681935325486294531 : ℤ) := by decide +kernel
theorem eP148_r : tableEnergyRadius t wP148 1 0 = (29521999969473543586620146992100203750877142206458336820636602448882949570908393327172820 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
