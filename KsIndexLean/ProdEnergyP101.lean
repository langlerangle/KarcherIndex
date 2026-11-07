module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP93

@[expose] public section

/-! Energy chunk P101: window [-1728,-1665] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP101 : Finset ℤ := Finset.Ioc (-1729) (-1665)
theorem eP101_c : tableEnergyNumerator t wP101 1 0 = (9808304261715244456319438764076453770090519564152536322990038159134984881562832382185033956679481 : ℤ) := by decide +kernel
theorem eP101_r : tableEnergyRadius t wP101 1 0 = (79875016724271493699373383416980966673627521454463024805918819130070487320614916131840258 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
