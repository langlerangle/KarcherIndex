module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P256: window [8192,8192] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP256 : Finset ℤ := Finset.Ioc (8191) (8192)
theorem eP256_c : tableEnergyNumerator t wP256 1 0 = (793015268674516238175387043546482101087659388044875759154738194103606722695095380233161518930 : ℤ) := by decide +kernel
theorem eP256_r : tableEnergyRadius t wP256 1 0 = (19307327977062239836933224080934137560784782829932803073140728942917804890252124553513 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
