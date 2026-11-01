module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P200: window [4608,4671] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP200 : Finset ℤ := Finset.Ioc (4607) (4671)
theorem eP200_c : tableEnergyNumerator t wP200 1 0 = (124379563310795431909789905125702418433065973927821786609066399059937600955182954801948385288832 : ℤ) := by decide +kernel
theorem eP200_r : tableEnergyRadius t wP200 1 0 = (3365475062241259802630692995391967428087489261629859524163739776376770484384385805279791 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
