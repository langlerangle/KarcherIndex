module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P238: window [7040,7103] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP238 : Finset ℤ := Finset.Ioc (7039) (7103)
theorem eP238_c : tableEnergyNumerator t wP238 1 0 = (64155791326267366479706774593939977557408577941359045370139918435376126717140109286957290349037 : ℤ) := by decide +kernel
theorem eP238_r : tableEnergyRadius t wP238 1 0 = (1603084710999135801315368826529347403449573539057722572090265923569872223405856561646395 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
