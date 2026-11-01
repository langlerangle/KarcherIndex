module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P25: window [-6592,-6529] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP25 : Finset ℤ := Finset.Ioc (-6593) (-6529)
theorem eP25_c : tableEnergyNumerator t wP25 1 0 = (690302983369948634096581151591239834987985298734856936503505460812365209745956268608514329141241 : ℤ) := by decide +kernel
theorem eP25_r : tableEnergyRadius t wP25 1 0 = (5656684411604405503071964064537991088081551262985998971385190829128365824262369464851615 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
