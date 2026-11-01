module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P89: window [-2496,-2433] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP89 : Finset ℤ := Finset.Ioc (-2497) (-2433)
theorem eP89_c : tableEnergyNumerator t wP89 1 0 = (4706079233267806475900211652137597597386413034063324204358599736962381796875418574871932612720319 : ℤ) := by decide +kernel
theorem eP89_r : tableEnergyRadius t wP89 1 0 = (38392255638516001460984506129143637369647650577811845997862284189586266947350813006560041 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
