module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P112: window [-1024,-961] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP112 : Finset ℤ := Finset.Ioc (-1025) (-961)
theorem eP112_c : tableEnergyNumerator t wP112 1 0 = (28221033673659296143072666901186414400965283222842432687245254659819975354461483681023547612006887 : ℤ) := by decide +kernel
theorem eP112_r : tableEnergyRadius t wP112 1 0 = (229222245221223478662584634519409923989434260813450746620575577421856111481460255507410615 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
