module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P232: window [6656,6719] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP232 : Finset ℤ := Finset.Ioc (6655) (6719)
theorem eP232_c : tableEnergyNumerator t wP232 1 0 = (70094308347512292761838119963576428319953023063315618903560875938851104163538604370676258557453 : ℤ) := by decide +kernel
theorem eP232_r : tableEnergyRadius t wP232 1 0 = (1769239068946097780640388830804895056795140551454898361456213118879383991906559643139465 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
