module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P236: window [6912,6975] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP236 : Finset ℤ := Finset.Ioc (6911) (6975)
theorem eP236_c : tableEnergyNumerator t wP236 1 0 = (66042863247282744022425077411943640953080608421355458431409389492571418491423764388792982733656 : ℤ) := by decide +kernel
theorem eP236_r : tableEnergyRadius t wP236 1 0 = (1655671769358737179974809486446910695605310262982278830249133535186118954070085903757786 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
