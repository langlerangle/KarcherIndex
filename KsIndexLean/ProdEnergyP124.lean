module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P124: window [-256,-193] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP124 : Finset ℤ := Finset.Ioc (-257) (-193)
theorem eP124_c : tableEnergyNumerator t wP124 1 0 = (545358018149873485025158697501396941047169811229897700453235098863249801533548045087600249981261956 : ℤ) := by decide +kernel
theorem eP124_r : tableEnergyRadius t wP124 1 0 = (4394466083194470811070029014379964807037237634679973382082542884203073518878046362686177574 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
