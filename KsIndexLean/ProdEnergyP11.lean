module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP3

@[expose] public section

/-! Energy chunk P11: window [-7488,-7425] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP11 : Finset ℤ := Finset.Ioc (-7489) (-7425)
theorem eP11_c : tableEnergyNumerator t wP11 1 0 = (537405458234838084326951145418152075069876969369360716890853036224282560511332635167654840722802 : ℤ) := by decide +kernel
theorem eP11_r : tableEnergyRadius t wP11 1 0 = (4406259971952648749025274798397278349348574138538333497893523927592720904381333290370222 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
