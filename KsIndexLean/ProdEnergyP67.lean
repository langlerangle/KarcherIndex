module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P67: window [-3904,-3841] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP67 : Finset ℤ := Finset.Ioc (-3905) (-3841)
theorem eP67_c : tableEnergyNumerator t wP67 1 0 = (1938372240581470445328850069670581968686515801810673829898408452136098749598179047929431691662454 : ℤ) := by decide +kernel
theorem eP67_r : tableEnergyRadius t wP67 1 0 = (15846335598755541023383051595501970674920553971893777765079200542814452125099053654107232 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
