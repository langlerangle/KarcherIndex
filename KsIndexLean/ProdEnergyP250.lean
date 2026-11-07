module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP242

@[expose] public section

/-! Energy chunk P250: window [7808,7871] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP250 : Finset ℤ := Finset.Ioc (7807) (7871)
theorem eP250_c : tableEnergyNumerator t wP250 1 0 = (54446558336666215552950849729197442068342008781761196915956602997837250681856499546434050890938 : ℤ) := by decide +kernel
theorem eP250_r : tableEnergyRadius t wP250 1 0 = (1335810429776472360552795230272446415531123207309048189065090807495115105208603441904715 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
