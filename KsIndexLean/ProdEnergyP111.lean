module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP103

@[expose] public section

/-! Energy chunk P111: window [-1088,-1025] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP111 : Finset ℤ := Finset.Ioc (-1089) (-1025)
theorem eP111_c : tableEnergyNumerator t wP111 1 0 = (24945764505629868803521326987850315076806950812093921837321127424326649620377214647913248327718081 : ℤ) := by decide +kernel
theorem eP111_r : tableEnergyRadius t wP111 1 0 = (202681859416341629577354443596406206623129244787026332414334983370220853311591984006504042 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
