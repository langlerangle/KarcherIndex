module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P128: window [0,63] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP128 : Finset ℤ := Finset.Ioc (-1) (63)
theorem eP128_c : tableEnergyNumerator t wP128 1 0 = (-2955514949730858343274309595015995630510206892898199184949950281222594162162123779977712027963070888994 : ℤ) := by decide +kernel
theorem eP128_r : tableEnergyRadius t wP128 1 0 = (25156231310086584505507507207379184738968855689264851466795066514364904569917258207253481167561 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
