module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P168: window [2560,2623] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP168 : Finset ℤ := Finset.Ioc (2559) (2623)
theorem eP168_c : tableEnergyNumerator t wP168 1 0 = (302099510781778857223508198118161776058088083676680455418876024817844534744220464213611929788833 : ℤ) := by decide +kernel
theorem eP168_r : tableEnergyRadius t wP168 1 0 = (9261519312854210216840135292834436978343655708173779278960790512227828183743716063804458 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
