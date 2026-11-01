module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P210: window [5248,5311] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP210 : Finset ℤ := Finset.Ioc (5247) (5311)
theorem eP210_c : tableEnergyNumerator t wP210 1 0 = (101691055724685393641500717423832246690161687601940235916197446290119602990677851034911956225525 : ℤ) := by decide +kernel
theorem eP210_r : tableEnergyRadius t wP210 1 0 = (2682885141613166358966056285149378113239806910710887348920888335638056850451906621933643 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
