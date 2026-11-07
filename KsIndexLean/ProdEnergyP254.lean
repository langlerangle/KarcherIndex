module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP246

@[expose] public section

/-! Energy chunk P254: window [8064,8127] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP254 : Finset ℤ := Finset.Ioc (8063) (8127)
theorem eP254_c : tableEnergyNumerator t wP254 1 0 = (51723790568721662402423425232226276166451421473944256014631313661436205730577423185576953106674 : ℤ) := by decide +kernel
theorem eP254_r : tableEnergyRadius t wP254 1 0 = (1261904502232522634359447032137906458654049186475354164660311526682838050042994881423404 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
