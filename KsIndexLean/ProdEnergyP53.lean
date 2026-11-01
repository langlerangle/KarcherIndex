module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P53: window [-4800,-4737] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP53 : Finset ℤ := Finset.Ioc (-4801) (-4737)
theorem eP53_c : tableEnergyNumerator t wP53 1 0 = (1289086555420752481230658980642685469675592303295125018986782038423309160379321396976368261841869 : ℤ) := by decide +kernel
theorem eP53_r : tableEnergyRadius t wP53 1 0 = (10548340201495559712841924469089722919517514839937929946353031545608767818588957760326263 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
