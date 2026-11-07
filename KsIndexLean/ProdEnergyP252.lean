module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP244

@[expose] public section

/-! Energy chunk P252: window [7936,7999] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP252 : Finset ℤ := Finset.Ioc (7935) (7999)
theorem eP252_c : tableEnergyNumerator t wP252 1 0 = (53057275755162698405808401719411148271011369472401055265684174601247463525435798305024432503939 : ℤ) := by decide +kernel
theorem eP252_r : tableEnergyRadius t wP252 1 0 = (1298040324936907550913572548202347417315825645173890583970840618889250364402298234796053 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
