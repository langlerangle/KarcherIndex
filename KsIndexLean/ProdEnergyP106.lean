module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP98

@[expose] public section

/-! Energy chunk P106: window [-1408,-1345] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP106 : Finset ℤ := Finset.Ioc (-1409) (-1345)
theorem eP106_c : tableEnergyNumerator t wP106 1 0 = (14804131459256260415937423540372366010603555708116595581844081235487825076018803985343725529001366 : ℤ) := by decide +kernel
theorem eP106_r : tableEnergyRadius t wP106 1 0 = (120437814108715063112907510166652180889651226763124779730207472683773895981815118335069300 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
