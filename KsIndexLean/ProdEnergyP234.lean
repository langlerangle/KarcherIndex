module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P234: window [6784,6847] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP234 : Finset ℤ := Finset.Ioc (6783) (6847)
theorem eP234_c : tableEnergyNumerator t wP234 1 0 = (68020341610876988498757287338044452938041004432570237444841230796701514399012654958528633611970 : ℤ) := by decide +kernel
theorem eP234_r : tableEnergyRadius t wP234 1 0 = (1710991065463558462975208445284896112940186032482204461425982313213937417212491027605558 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
