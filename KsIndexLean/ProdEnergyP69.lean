module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P69: window [-3776,-3713] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP69 : Finset ℤ := Finset.Ioc (-3777) (-3713)
theorem eP69_c : tableEnergyNumerator t wP69 1 0 = (2070437369181284995153564994285340901075863346802215472272856927538857689047694262951640313032539 : ℤ) := by decide +kernel
theorem eP69_r : tableEnergyRadius t wP69 1 0 = (16923378017832681524675532842933800713368035525466682973907397827345113014949787241948985 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
