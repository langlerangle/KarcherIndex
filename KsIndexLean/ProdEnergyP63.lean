module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P63: window [-4160,-4097] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP63 : Finset ℤ := Finset.Ioc (-4161) (-4097)
theorem eP63_c : tableEnergyNumerator t wP63 1 0 = (1709752735525658921530061669293907175768996557041454298601118831720049871729461772412245020822157 : ℤ) := by decide +kernel
theorem eP63_r : tableEnergyRadius t wP63 1 0 = (13981433024405164508764934051289821342963042705478796682276226504673446076531104054075134 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
