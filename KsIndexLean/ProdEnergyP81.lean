module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP73

@[expose] public section

/-! Energy chunk P81: window [-3008,-2945] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP81 : Finset ℤ := Finset.Ioc (-3009) (-2945)
theorem eP81_c : tableEnergyNumerator t wP81 1 0 = (3248321035366675353039396362289972010632372001690779230001099935869565891824070027952273061647205 : ℤ) := by decide +kernel
theorem eP81_r : tableEnergyRadius t wP81 1 0 = (26523146868021904985770719288231641401893491958275542748039528116314401688286535755216851 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
