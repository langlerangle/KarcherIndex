module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP190

@[expose] public section

/-! Energy chunk P198: window [4480,4543] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP198 : Finset ℤ := Finset.Ioc (4479) (4543)
theorem eP198_c : tableEnergyNumerator t wP198 1 0 = (129897232743198811773441215495426802998367636975440830842070683236715311510398160508328113234293 : ℤ) := by decide +kernel
theorem eP198_r : tableEnergyRadius t wP198 1 0 = (3534439366616795719432845235420839928029966060282646213852235027368417892018554172831721 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
