module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P41: window [-5568,-5505] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP41 : Finset ℤ := Finset.Ioc (-5569) (-5505)
theorem eP41_c : tableEnergyNumerator t wP41 1 0 = (962222154428757389098721037409860253233706276137198666428609696386474485862733758752000942762309 : ℤ) := by decide +kernel
theorem eP41_r : tableEnergyRadius t wP41 1 0 = (7878962052181263485917854851398821154521705508665621596912843875141025891896533681348448 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
