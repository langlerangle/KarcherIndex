module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P125: window [-192,-129] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP125 : Finset ℤ := Finset.Ioc (-193) (-129)
theorem eP125_c : tableEnergyNumerator t wP125 1 0 = (1084239062976094829690220533151043496536713503539886303870197632271713560812806124409952704455541534 : ℤ) := by decide +kernel
theorem eP125_r : tableEnergyRadius t wP125 1 0 = (8718351990215116618935536824691887673826228612771643494915799333836306871069055608489144427 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
