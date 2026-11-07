module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP170

@[expose] public section

/-! Energy chunk P178: window [3200,3263] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP178 : Finset ℤ := Finset.Ioc (3199) (3263)
theorem eP178_c : tableEnergyNumerator t wP178 1 0 = (216726182761331599475852715791469902276784432665959819827937345028059805423095328351603564509821 : ℤ) := by decide +kernel
theorem eP178_r : tableEnergyRadius t wP178 1 0 = (6322735741933518500994297331393495837996247755234619663733521002624572774966457965377377 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
