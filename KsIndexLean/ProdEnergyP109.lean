module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P109: window [-1216,-1153] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP109 : Finset ℤ := Finset.Ioc (-1217) (-1153)
theorem eP109_c : tableEnergyNumerator t wP109 1 0 = (19906956346531312074681176309567103702654426601459061983988364979039143547184337831374719214181129 : ℤ) := by decide +kernel
theorem eP109_r : tableEnergyRadius t wP109 1 0 = (161832974456613714641130913862495181291755658938614526040774375216613842395259646122144918 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
