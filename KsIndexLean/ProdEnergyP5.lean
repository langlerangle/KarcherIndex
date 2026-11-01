module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P5: window [-7872,-7809] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP5 : Finset ℤ := Finset.Ioc (-7873) (-7809)
theorem eP5_c : tableEnergyNumerator t wP5 1 0 = (487152584183627684223031741182600218795534884422325742017283059354222034757040713773477660368924 : ℤ) := by decide +kernel
theorem eP5_r : tableEnergyRadius t wP5 1 0 = (3995112569095852407352883728491091284830238373624313544768012262820434205583055735346781 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
