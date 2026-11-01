module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P1: window [-8128,-8065] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP1 : Finset ℤ := Finset.Ioc (-8129) (-8065)
theorem eP1_c : tableEnergyNumerator t wP1 1 0 = (457498731444564357909815646392460925955984542178611202006257990308580456665860363385414963572413 : ℤ) := by decide +kernel
theorem eP1_r : tableEnergyRadius t wP1 1 0 = (3752452180490401091358784509434813961349525077414918782160467101974846858902513702664486 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
