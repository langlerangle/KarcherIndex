module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P71: window [-3648,-3585] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP71 : Finset ℤ := Finset.Ioc (-3649) (-3585)
theorem eP71_c : tableEnergyNumerator t wP71 1 0 = (2216599509406684731789179068895399591295786821382270633251799326720954844909641384014292775948375 : ℤ) := by decide +kernel
theorem eP71_r : tableEnergyRadius t wP71 1 0 = (18115195766694774591548884913878609055608212484840288656367770814294743092271160577863738 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
