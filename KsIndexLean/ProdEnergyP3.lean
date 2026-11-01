module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P3: window [-8000,-7937] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP3 : Finset ℤ := Finset.Ioc (-8001) (-7937)
theorem eP3_c : tableEnergyNumerator t wP3 1 0 = (471973327229535539952547031429379792328926280546368122587149628978033375766597962125963907920379 : ℤ) := by decide +kernel
theorem eP3_r : tableEnergyRadius t wP3 1 0 = (3870903606765033851583821362064719011779540071191137783380047126119637600461297714491719 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
