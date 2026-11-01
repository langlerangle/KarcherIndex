module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P146: window [1152,1215] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP146 : Finset ℤ := Finset.Ioc (1151) (1215)
theorem eP146_c : tableEnergyNumerator t wP146 1 0 = (932391710571648748109542569835814260066721873915021100981850276005408937987154542874593705462392 : ℤ) := by decide +kernel
theorem eP146_r : tableEnergyRadius t wP146 1 0 = (35057454084532538990716305618099945935446389729576329646846042469939760436614040847812364 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
