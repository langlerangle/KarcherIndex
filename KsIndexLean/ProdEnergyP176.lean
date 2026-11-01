module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P176: window [3072,3135] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP176 : Finset ℤ := Finset.Ioc (3071) (3135)
theorem eP176_c : tableEnergyNumerator t wP176 1 0 = (230409962904589180523095768203443043033917820182435728181928076529173958104468340619372463300798 : ℤ) := by decide +kernel
theorem eP176_r : tableEnergyRadius t wP176 1 0 = (6781779034013958228465941461758677967058419723151265716217836937281961977167754795240133 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
