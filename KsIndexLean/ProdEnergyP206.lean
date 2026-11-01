module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P206: window [4992,5055] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP206 : Finset ℤ := Finset.Ioc (4991) (5055)
theorem eP206_c : tableEnergyNumerator t wP206 1 0 = (109900828271069165637931673609335636777060628550000951872980005715998098617475623229406781692854 : ℤ) := by decide +kernel
theorem eP206_r : tableEnergyRadius t wP206 1 0 = (2927531644696691073253548137530390583213756180931088534104869415431876050454601926861845 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
