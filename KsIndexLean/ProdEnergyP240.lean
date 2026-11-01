module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P240: window [7168,7231] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP240 : Finset ℤ := Finset.Ioc (7167) (7231)
theorem eP240_c : tableEnergyNumerator t wP240 1 0 = (62353524750361369967205544482280264164297671266132872145231378535539076644906995441784555034658 : ℤ) := by decide +kernel
theorem eP240_r : tableEnergyRadius t wP240 1 0 = (1553049793601326327913811265795862339439013341165447373011396925440443014653736150730332 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
