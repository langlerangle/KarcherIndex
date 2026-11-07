module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP11

@[expose] public section

/-! Energy chunk P19: window [-6976,-6913] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP19 : Finset ℤ := Finset.Ioc (-6977) (-6913)
theorem eP19_c : tableEnergyNumerator t wP19 1 0 = (617613492212703889701326582711944039860794623464398799525480056655218838989873297709349199450508 : ℤ) := by decide +kernel
theorem eP19_r : tableEnergyRadius t wP19 1 0 = (5062306346387503885787992428821426040164968801681492007098019107391693611458200954571372 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
