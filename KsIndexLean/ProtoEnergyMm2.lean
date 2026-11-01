module

public import KsIndexLean.ProtoAccessor

@[expose] public section

/-! Energy chunk Mm2: window [64,64] of component (a,b)=(4,1). -/
namespace KsIndex.NegSignProto
open KsIndex.AlphaRemarkTrial
def wMm2 : Finset ℤ := Finset.Ioc (63) (64)
theorem eMm2_c : tableEnergyNumerator t wMm2 4 1 = (64721700708258424828686052904669061183091462035786272143099697694144005898001344110099568785081975 : ℤ) := by decide +kernel
theorem eMm2_r : tableEnergyRadius t wMm2 4 1 = (258382239217986721842467890651456865963375134143781089165120184117038706791064674695764614 : ℤ) := by decide +kernel
end KsIndex.NegSignProto
