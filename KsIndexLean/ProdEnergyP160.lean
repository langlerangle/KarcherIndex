module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP152

@[expose] public section

/-! Energy chunk P160: window [2048,2111] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP160 : Finset ℤ := Finset.Ioc (2047) (2111)
theorem eP160_c : tableEnergyNumerator t wP160 1 0 = (418285248603609196102214346653677213488103719731193097819837317861704253422158963294480513101359 : ℤ) := by decide +kernel
theorem eP160_r : tableEnergyRadius t wP160 1 0 = (13515719233451094982776135960241387150958134103656296642924092603427169007074972489262083 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
