module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP118

@[expose] public section

/-! Energy chunk P126: window [-128,-65] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP126 : Finset ℤ := Finset.Ioc (-129) (-65)
theorem eP126_c : tableEnergyNumerator t wP126 1 0 = (3224427336589679949340640816315530422234951453564606188559606710814555528643065473527663853022044782 : ℤ) := by decide +kernel
theorem eP126_r : tableEnergyRadius t wP126 1 0 = (25829566840727983783163190204484886978636991890705040244056296049726275575759288202403429981 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
