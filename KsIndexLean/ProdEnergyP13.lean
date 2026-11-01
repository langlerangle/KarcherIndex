module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P13: window [-7360,-7297] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP13 : Finset ℤ := Finset.Ioc (-7361) (-7297)
theorem eP13_c : tableEnergyNumerator t wP13 1 0 = (555911894999506005860805462265529205854603417818352832253127980975128484489167702988131019252340 : ℤ) := by decide +kernel
theorem eP13_r : tableEnergyRadius t wP13 1 0 = (4557648830751464385901917067803218894813578797858661509072556135658186865359164337915674 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
