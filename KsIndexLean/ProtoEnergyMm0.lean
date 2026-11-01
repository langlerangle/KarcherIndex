module

public import KsIndexLean.ProtoAccessor

@[expose] public section

/-! Energy chunk Mm0: window [-64,-1] of component (a,b)=(4,1). -/
namespace KsIndex.NegSignProto
open KsIndex.AlphaRemarkTrial
def wMm0 : Finset ℤ := Finset.Ioc (-65) (-1)
theorem eMm0_c : tableEnergyNumerator t wMm0 4 1 = (6951262644557965972127843338874322790676187012668876645625062207054521683635927775523248857475611444 : ℤ) := by decide +kernel
theorem eMm0_r : tableEnergyRadius t wMm0 4 1 = (473398355081867105119701203653754897392325480641596550947842567227807724522248821561316706778 : ℤ) := by decide +kernel
end KsIndex.NegSignProto
