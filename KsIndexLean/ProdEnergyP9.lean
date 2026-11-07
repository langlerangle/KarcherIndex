module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP1

@[expose] public section

/-! Energy chunk P9: window [-7616,-7553] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP9 : Finset ℤ := Finset.Ioc (-7617) (-7553)
theorem eP9_c : tableEnergyNumerator t wP9 1 0 = (519815829163345430157039815586119874224125572226724971971334551364536101595979268888804967609502 : ℤ) := by decide +kernel
theorem eP9_r : tableEnergyRadius t wP9 1 0 = (4262359739502126916462922287754141572534957271312394996685978521435225393550186718801088 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
