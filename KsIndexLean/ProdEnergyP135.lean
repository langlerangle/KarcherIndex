module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P135: window [448,511] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP135 : Finset ℤ := Finset.Ioc (447) (511)
theorem eP135_c : tableEnergyNumerator t wP135 1 0 = (2941107780722588724757072699649904735506620266505227756054392615574088633834460170270104792053949 : ℤ) := by decide +kernel
theorem eP135_r : tableEnergyRadius t wP135 1 0 = (151551573334171349206687774913946510173726189833759778705436928761429773808253242619704868 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
