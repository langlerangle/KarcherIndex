module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP222

@[expose] public section

/-! Energy chunk P230: window [6528,6591] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP230 : Finset ℤ := Finset.Ioc (6527) (6591)
theorem eP230_c : tableEnergyNumerator t wP230 1 0 = (72271377412524970866661147002163115518583355393129938734208790947607857337997367126976504389845 : ℤ) := by decide +kernel
theorem eP230_r : tableEnergyRadius t wP230 1 0 = (1830630457244093613064889776306216223647945667906537838177320840291794137440486557957677 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
