module

public import KsIndexLean.ProtoAccessor

@[expose] public section

/-! Energy chunk P2: window [64,64] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProto
open KsIndex.AlphaRemarkTrial
def wP2 : Finset ℤ := Finset.Ioc (63) (64)
theorem eP2_c : tableEnergyNumerator t wP2 1 0 = (49127069667962168968629478407608351944688888533289637333392078578726707863950853080095447598885 : ℤ) := by decide +kernel
theorem eP2_r : tableEnergyRadius t wP2 1 0 = (17928131296323613774348674430522461261147873227755291783241537305961490659340052783831310 : ℤ) := by decide +kernel
end KsIndex.NegSignProto
