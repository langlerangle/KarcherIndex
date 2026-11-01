module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P61: window [-4288,-4225] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP61 : Finset ℤ := Finset.Ioc (-4289) (-4225)
theorem eP61_c : tableEnergyNumerator t wP61 1 0 = (1610429358128570183540176415314042066956533227471717378035044003127285100424800749918021066661481 : ℤ) := by decide +kernel
theorem eP61_r : tableEnergyRadius t wP61 1 0 = (13171048296998656113012822316357234873773147277133563219684248464703401125805559810121124 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
