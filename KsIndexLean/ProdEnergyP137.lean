module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P137: window [576,639] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP137 : Finset ℤ := Finset.Ioc (575) (639)
theorem eP137_c : tableEnergyNumerator t wP137 1 0 = (2223641189419811976641437067636055265829448401333568699114295340406304131892016729219416286135074 : ℤ) := by decide +kernel
theorem eP137_r : tableEnergyRadius t wP137 1 0 = (104322425643432633680927860785255415581145008373717153300920465772103041821142178563301066 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
