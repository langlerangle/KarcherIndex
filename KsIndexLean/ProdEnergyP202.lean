module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P202: window [4736,4799] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP202 : Finset ℤ := Finset.Ioc (4735) (4799)
theorem eP202_c : tableEnergyNumerator t wP202 1 0 = (119228921809534594338377018392834856900432181570937824134865703550535015885757163192379130145082 : ℤ) := by decide +kernel
theorem eP202_r : tableEnergyRadius t wP202 1 0 = (3208763891126277811609007119086544154752067709297083539372542259074329905325926194630980 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
