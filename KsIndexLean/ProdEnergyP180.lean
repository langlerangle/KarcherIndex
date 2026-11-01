module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P180: window [3328,3391] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP180 : Finset ℤ := Finset.Ioc (3327) (3391)
theorem eP180_c : tableEnergyNumerator t wP180 1 0 = (204306786088587873552344471489198617220353569135951478216050085567106735923743883621657859994670 : ℤ) := by decide +kernel
theorem eP180_r : tableEnergyRadius t wP180 1 0 = (5910387352700985598242480842021321134378294670373643607723011757146562691232791671310209 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
