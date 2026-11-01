module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P131: window [192,255] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP131 : Finset ℤ := Finset.Ioc (191) (255)
theorem eP131_c : tableEnergyNumerator t wP131 1 0 = (6127493923268140041269859138851753195963892344113729964737174936472418800741107546234617199641163 : ℤ) := by decide +kernel
theorem eP131_r : tableEnergyRadius t wP131 1 0 = (467623600191900829268877733853691887185138751213708036887500543582005765882148783916874870 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
