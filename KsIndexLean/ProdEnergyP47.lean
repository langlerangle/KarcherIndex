module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP39

@[expose] public section

/-! Energy chunk P47: window [-5184,-5121] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP47 : Finset ℤ := Finset.Ioc (-5185) (-5121)
theorem eP47_c : tableEnergyNumerator t wP47 1 0 = (1107643300330532134133941023489972183411939292317619052861070306739204023248790820662115126414965 : ℤ) := by decide +kernel
theorem eP47_r : tableEnergyRadius t wP47 1 0 = (9066789021313321985152612153507658743048749694170446640726041205667664739500687520540049 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
