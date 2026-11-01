module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P85: window [-2752,-2689] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP85 : Finset ℤ := Finset.Ioc (-2753) (-2689)
theorem eP85_c : tableEnergyNumerator t wP85 1 0 = (3875683860658625563966181936344776262833706325799763565279748905474706862582543049375438342460536 : ℤ) := by decide +kernel
theorem eP85_r : tableEnergyRadius t wP85 1 0 = (31632468800384848390428755331699720531902301587136873874122672386784550186472265155768824 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
