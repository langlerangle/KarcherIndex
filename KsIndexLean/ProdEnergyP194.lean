module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P194: window [4224,4287] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP194 : Finset ℤ := Finset.Ioc (4223) (4287)
theorem eP194_c : tableEnergyNumerator t wP194 1 0 = (142187180919220640962481506612697170401958521321800151399743052838843492724424688834888000580348 : ℤ) := by decide +kernel
theorem eP194_r : tableEnergyRadius t wP194 1 0 = (3914678540072560182678426453399816821791021504321014092264697685102940116206741297138785 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
