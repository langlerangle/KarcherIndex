module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP110

@[expose] public section

/-! Energy chunk P118: window [-640,-577] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP118 : Finset ℤ := Finset.Ioc (-641) (-577)
theorem eP118_c : tableEnergyNumerator t wP118 1 0 = (74281366031808377613744744057496819118933796029015897030224847765385334295232874299236270188004485 : ℤ) := by decide +kernel
theorem eP118_r : tableEnergyRadius t wP118 1 0 = (601852038292089560781566126419809210716726944788715104852221275878188903527830284086191629 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
