module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP150

@[expose] public section

/-! Energy chunk P158: window [1920,1983] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP158 : Finset ℤ := Finset.Ioc (1919) (1983)
theorem eP158_c : tableEnergyNumerator t wP158 1 0 = (458934890271065542210130162805850553812100990053876894556758255633493784844861714897767252999284 : ℤ) := by decide +kernel
theorem eP158_r : tableEnergyRadius t wP158 1 0 = (15065425693259040386839661474561330403647044676095176314769070851779168319790168498173323 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
