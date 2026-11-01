module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P123: window [-320,-257] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP123 : Finset ℤ := Finset.Ioc (-321) (-257)
theorem eP123_c : tableEnergyNumerator t wP123 1 0 = (328783064710344360639040341810421428494268279750572016523768603636637717243960590678420798867823871 : ℤ) := by decide +kernel
theorem eP123_r : tableEnergyRadius t wP123 1 0 = (2653199208870186388351770987587161623721463130656775396707997371162936237928836337759949159 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
