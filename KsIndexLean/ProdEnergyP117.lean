module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P117: window [-704,-641] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP117 : Finset ℤ := Finset.Ioc (-705) (-641)
theorem eP117_c : tableEnergyNumerator t wP117 1 0 = (60928750067716251434545266193033833594924559351516001882078000060793661587320629583494322133467143 : ℤ) := by decide +kernel
theorem eP117_r : tableEnergyRadius t wP117 1 0 = (493918551211186518707570234667909486967507253792718132036781657967505856800941111731474738 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
