module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP182

@[expose] public section

/-! Energy chunk P190: window [3968,4031] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP190 : Finset ℤ := Finset.Ioc (3967) (4031)
theorem eP190_c : tableEnergyNumerator t wP190 1 0 = (156460364823264127222769856866417359987686468069680933160379558309652124647849763041354107826956 : ℤ) := by decide +kernel
theorem eP190_r : tableEnergyRadius t wP190 1 0 = (4362703854293867630968126075619638748895590099204016267617654610984276022200698231988205 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
