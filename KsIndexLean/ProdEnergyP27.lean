module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP19

@[expose] public section

/-! Energy chunk P27: window [-6464,-6401] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP27 : Finset ℤ := Finset.Ioc (-6465) (-6401)
theorem eP27_c : tableEnergyNumerator t wP27 1 0 = (717432251137044545421175761496363003130010993232525791469907303348013478443396348961542227514222 : ℤ) := by decide +kernel
theorem eP27_r : tableEnergyRadius t wP27 1 0 = (5878480812720161372144714858749963714795703324789295510600663855160472779691651433129037 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
