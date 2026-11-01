module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P222: window [6016,6079] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP222 : Finset ℤ := Finset.Ioc (6015) (6079)
theorem eP222_c : tableEnergyNumerator t wP222 1 0 = (82165030803709739126368887868220307845576404029582129086409354601213096345838537338017187095877 : ℤ) := by decide +kernel
theorem eP222_r : tableEnergyRadius t wP222 1 0 = (2112685561977407430534376469182036820096143622919298157440397987076350094864618398665229 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
