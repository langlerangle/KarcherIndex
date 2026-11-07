module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP47

@[expose] public section

/-! Energy chunk P55: window [-4672,-4609] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP55 : Finset ℤ := Finset.Ioc (-4673) (-4609)
theorem eP55_c : tableEnergyNumerator t wP55 1 0 = (1359668180126548084884166643427420177372623114697202169604096594903810534131367466573831005553110 : ℤ) := by decide +kernel
theorem eP55_r : tableEnergyRadius t wP55 1 0 = (11124528039563539070998165016210915253576759678698869288313664819986012904289555153186126 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
