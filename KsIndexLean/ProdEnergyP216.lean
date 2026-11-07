module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP208

@[expose] public section

/-! Energy chunk P216: window [5632,5695] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP216 : Finset ℤ := Finset.Ioc (5631) (5695)
theorem eP216_c : tableEnergyNumerator t wP216 1 0 = (91095597542779586693864084482350399259610066895159988400871279058069972619423669689064145871778 : ℤ) := by decide +kernel
theorem eP216_r : tableEnergyRadius t wP216 1 0 = (2371350997981496683968391532695127090379756946514082738115675788178699589580534952079954 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
