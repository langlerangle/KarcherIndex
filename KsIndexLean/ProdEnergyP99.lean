module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP91

@[expose] public section

/-! Energy chunk P99: window [-1856,-1793] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP99 : Finset ℤ := Finset.Ioc (-1857) (-1793)
theorem eP99_c : tableEnergyNumerator t wP99 1 0 = (8500069534717807174948436498413261213198348725921053879382121053540449602798040230660909575617738 : ℤ) := by decide +kernel
theorem eP99_r : tableEnergyRadius t wP99 1 0 = (69245300984983786881128814041734951536643136586788268012715807930302962361897180938289151 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
