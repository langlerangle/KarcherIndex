module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P192: window [4096,4159] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP192 : Finset ℤ := Finset.Ioc (4095) (4159)
theorem eP192_c : tableEnergyNumerator t wP192 1 0 = (149049404801116615614580534919054222503097532968654730451496284370160032787702752810816155637299 : ℤ) := by decide +kernel
theorem eP192_r : tableEnergyRadius t wP192 1 0 = (4129240233071192972841233852096987492203976015045799189629607560808523973437713020969010 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
