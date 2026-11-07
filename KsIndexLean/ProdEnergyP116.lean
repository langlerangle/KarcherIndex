module

public import KsIndexLean.ProdAccessor
import KsIndexLean.ProdEnergyP108

@[expose] public section

/-! Energy chunk P116: window [-768,-705] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP116 : Finset ℤ := Finset.Ioc (-769) (-705)
theorem eP116_c : tableEnergyNumerator t wP116 1 0 = (50893543896380869474363179462650488801182260014583809858771396466021651728331335387155622505115691 : ℤ) := by decide +kernel
theorem eP116_r : tableEnergyRadius t wP116 1 0 = (412759352061175316879394113929965457551392155434955715605881858922890971870410240510341109 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
