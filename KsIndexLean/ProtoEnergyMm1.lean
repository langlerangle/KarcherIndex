module

public import KsIndexLean.ProtoAccessor

@[expose] public section

/-! Energy chunk Mm1: window [0,63] of component (a,b)=(4,1). -/
namespace KsIndex.NegSignProto
open KsIndex.AlphaRemarkTrial
def wMm1 : Finset ℤ := Finset.Ioc (-1) (63)
theorem eMm1_c : tableEnergyNumerator t wMm1 4 1 = (1217405699524181951292345457616043138787509349542580579973584240074832411331878082223428617939286528268 : ℤ) := by decide +kernel
theorem eMm1_r : tableEnergyRadius t wMm1 4 1 = (7917808181881773866284461191362795477781205013335867728942796860038733831035753757152497787741 : ℤ) := by decide +kernel
end KsIndex.NegSignProto
