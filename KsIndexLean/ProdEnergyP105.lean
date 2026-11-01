module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P105: window [-1472,-1409] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP105 : Finset ℤ := Finset.Ioc (-1473) (-1409)
theorem eP105_c : tableEnergyNumerator t wP105 1 0 = (13536088043273952453880425551132976045525533070680077860954385428389747646022066160870590755829393 : ℤ) := by decide +kernel
theorem eP105_r : tableEnergyRadius t wP105 1 0 = (110145973641608715132743978353784662260242723305930639923376179962018793792253842917012536 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
