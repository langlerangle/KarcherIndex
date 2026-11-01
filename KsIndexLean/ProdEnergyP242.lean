module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P242: window [7296,7359] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP242 : Finset ℤ := Finset.Ioc (7295) (7359)
theorem eP242_c : tableEnergyNumerator t wP242 1 0 = (60630897771139683868894743722181815109350181116602652900470918259713332003308832423988903726691 : ℤ) := by decide +kernel
theorem eP242_r : tableEnergyRadius t wP242 1 0 = (1505401671511719824618052492972694580928524537167913537898502269856692435576399396181722 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
