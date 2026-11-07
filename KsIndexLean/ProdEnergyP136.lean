module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP128

@[expose] public section

/-! Energy chunk P136: window [512,575] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP136 : Finset ℤ := Finset.Ioc (511) (575)
theorem eP136_c : tableEnergyNumerator t wP136 1 0 = (2542082494962291346310105900008359548825102915492909021308667082100842341199819245312171819712989 : ℤ) := by decide +kernel
theorem eP136_r : tableEnergyRadius t wP136 1 0 = (124492696052937442075500504196061855980633104940821856541693897197547460565002916546008475 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
