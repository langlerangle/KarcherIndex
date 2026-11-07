module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP130

@[expose] public section

/-! Energy chunk P138: window [640,703] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP138 : Finset ℤ := Finset.Ioc (639) (703)
theorem eP138_c : tableEnergyNumerator t wP138 1 0 = (1965177926369809138529947708550954227355364350581333375575395542401158204283545773190780024419785 : ℤ) := by decide +kernel
theorem eP138_r : tableEnergyRadius t wP138 1 0 = (88852263673633573334274974053786463430142991536506807035289916934370579472139885207398143 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
