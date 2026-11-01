module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P133: window [320,383] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP133 : Finset ℤ := Finset.Ioc (319) (383)
theorem eP133_c : tableEnergyNumerator t wP133 1 0 = (4113350865553700617029595004085502425899391014219085820303438384686463382666665335534073647868005 : ℤ) := by decide +kernel
theorem eP133_r : tableEnergyRadius t wP133 1 0 = (243799898444842296094019578387457755642060526079788047488400918759663069582336138726761559 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
