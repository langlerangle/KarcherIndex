module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P156: window [1792,1855] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP156 : Finset ℤ := Finset.Ioc (1791) (1855)
theorem eP156_c : tableEnergyNumerator t wP156 1 0 = (506400755800427655244527274800435733180402592760689432839792768500974597464625266907998624300446 : ℤ) := by decide +kernel
theorem eP156_r : tableEnergyRadius t wP156 1 0 = (16912102826531222066125661916324168249110794192256146009339932085620029390257623438819528 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
