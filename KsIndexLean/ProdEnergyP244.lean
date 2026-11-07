module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP236

@[expose] public section

/-! Energy chunk P244: window [7424,7487] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP244 : Finset ℤ := Finset.Ioc (7423) (7487)
theorem eP244_c : tableEnergyNumerator t wP244 1 0 = (58983139492328417265614859520135871628324432649302424080752037275115859427095445995153698624849 : ℤ) := by decide +kernel
theorem eP244_r : tableEnergyRadius t wP244 1 0 = (1459988313763246968561290539146853363230532235900279284587367050973617014962838114109676 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
