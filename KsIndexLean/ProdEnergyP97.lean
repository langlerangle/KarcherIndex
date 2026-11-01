module

public import KsIndexLean.ProdAccessor

@[expose] public section

/-! Energy chunk P97: window [-1984,-1921] of component (a,b)=(1,0). -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial
def wP97 : Finset ℤ := Finset.Ioc (-1985) (-1921)
theorem eP97_c : tableEnergyNumerator t wP97 1 0 = (7438559424982652750909784553790546594471905858920781860957942753257801084785689267906956089817339 : ℤ) := by decide +kernel
theorem eP97_r : tableEnergyRadius t wP97 1 0 = (60617307949085771645209115440316931311436497411198003690858258153762911916669815196808657 : ℤ) := by decide +kernel
end KsIndex.NegSignProd
