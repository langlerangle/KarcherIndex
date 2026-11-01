module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P65: window [-4032,-3969] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP65 : Finset ℤ := Finset.Ioc (-4033) (-3969)
theorem eP65_c : tableEnergyNumerator t wP65 1 0 = (1818642208383320804915147617289527098826952265127624611296850915233403604016099003786894114027257 : ℤ) := by decide +kernel
theorem eP65_r : tableEnergyRadius t wP65 1 0 = (14869739440409955508498370576272328707008634722330149053624474344229559898044675500433716 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
