module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP142

@[expose] public section

/-! Energy chunk P150: window [1408,1471] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP150 : Finset ℤ := Finset.Ioc (1407) (1471)
theorem eP150_c : tableEnergyNumerator t wP150 1 0 = (709830947785538402404844049609550203839854564524600027537931745329604676352335832435368714455128 : ℤ) := by decide +kernel
theorem eP150_r : tableEnergyRadius t wP150 1 0 = (25243103007832823404309188070493002267151144586524508498024881646249689032655086073642345 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
