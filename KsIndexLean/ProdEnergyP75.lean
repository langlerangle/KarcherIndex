module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P75: window [-3392,-3329] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP75 : Finset ℤ := Finset.Ioc (-3393) (-3329)
theorem eP75_c : tableEnergyNumerator t wP75 1 0 = (2559973231059896684732189854075722544147672198082991579123833682741877103481080844360415619718397 : ℤ) := by decide +kernel
theorem eP75_r : tableEnergyRadius t wP75 1 0 = (20914371138722539542975735878016756667356506016703522024947716912335229836392458996650075 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
