module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P17: window [-7104,-7041] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP17 : Finset ℤ := Finset.Ioc (-7105) (-7041)
theorem eP17_c : tableEnergyNumerator t wP17 1 0 = (595941603488163468621318203302721980005624985706615988145009087944739178859844946715551889683824 : ℤ) := by decide +kernel
theorem eP17_r : tableEnergyRadius t wP17 1 0 = (4885065859453344972465582387082586374340063874826733626478625904584005972206811144275866 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
