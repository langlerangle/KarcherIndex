module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP154

@[expose] public section

/-! Energy chunk P162: window [2176,2239] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP162 : Finset ℤ := Finset.Ioc (2175) (2239)
theorem eP162_c : tableEnergyNumerator t wP162 1 0 = (383165313928628901970505627446220458512568537577891695261182743460340356164765508771171284682742 : ℤ) := by decide +kernel
theorem eP162_r : tableEnergyRadius t wP162 1 0 = (12201516825687655674109604094296624882535637127196960768976571198688205626920395519247144 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
