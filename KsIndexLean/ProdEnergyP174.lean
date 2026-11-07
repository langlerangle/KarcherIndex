module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP166

@[expose] public section

/-! Energy chunk P174: window [2944,3007] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP174 : Finset ℤ := Finset.Ioc (2943) (3007)
theorem eP174_c : tableEnergyNumerator t wP174 1 0 = (245543587259427750931394888067805730744654918524323050171880603247969774375237405715348904586709 : ℤ) := by decide +kernel
theorem eP174_r : tableEnergyRadius t wP174 1 0 = (7295017807371723268573925401059550701764417710199024443145438338395414102405555678155198 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
