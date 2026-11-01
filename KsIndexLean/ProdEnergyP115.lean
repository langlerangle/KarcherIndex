module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P115: window [-832,-769] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP115 : Finset ℤ := Finset.Ioc (-833) (-769)
theorem eP115_c : tableEnergyNumerator t wP115 1 0 = (43159128626837475933453837434229336469571770065995231169743733273571009866538143049596435437239331 : ℤ) := by decide +kernel
theorem eP115_r : tableEnergyRadius t wP115 1 0 = (350178848443600861728902313195219536836300620531137241744048108066073201660096953810001144 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
