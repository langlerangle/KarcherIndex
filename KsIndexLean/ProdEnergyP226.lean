module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP218

@[expose] public section

/-! Energy chunk P226: window [6272,6335] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP226 : Finset ℤ := Finset.Ioc (6271) (6335)
theorem eP226_c : tableEnergyNumerator t wP226 1 0 = (76964292452350207669188142028631207466031710131251732231786461898987974214734787846944613517234 : ℤ) := by decide +kernel
theorem eP226_r : tableEnergyRadius t wP226 1 0 = (1963805907825888392911446607812537434692546967997498939724003605890956381161943892014608 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
