module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P208: window [5120,5183] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP208 : Finset ℤ := Finset.Ioc (5119) (5183)
theorem eP208_c : tableEnergyNumerator t wP208 1 0 = (105668127520469157923323960689344863089253434466270986127779801304233137383775646634607578891327 : ℤ) := by decide +kernel
theorem eP208_r : tableEnergyRadius t wP208 1 0 = (2801055173590796917811284441201779088207430962861016924947902376375206692177213087033855 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
