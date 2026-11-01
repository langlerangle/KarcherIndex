module

public import KsIndexLean.ProtoAccessor

@[expose] public section

/-! Energy chunk P1: window [0,63] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProto
open KsIndex.AlphaRemarkTrial
def wP1 : Finset ℤ := Finset.Ioc (-1) (63)
theorem eP1_c : tableEnergyNumerator t wP1 1 0 = (-2955514949730858343274309595015995630510206892898199184949950281222594162162123779977712027963070888994 : ℤ) := by decide +kernel
theorem eP1_r : tableEnergyRadius t wP1 1 0 = (25156231310086584505507507207379184738968855689264851466795066514364904569917258207253481167561 : ℤ) := by decide +kernel
end KsIndex.NegSignProto
