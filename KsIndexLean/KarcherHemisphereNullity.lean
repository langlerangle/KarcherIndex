module

public import KsIndexLean.KarcherHalfPeriodRadical
public import KsIndexLean.HemisphereWeakRadical

@[expose] public section


/-! Pure half-period nullity transported to the actual single lower hemisphere. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.Spherical
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Actual bounded geometric half-period fields and the full-test lower
hemisphere Jacobi kernel correspond in each pure D/N rotation character. -/
def classicalHalfPeriodHemisphereEquiv (R : PaperHalfPeriodRealization k) (b : Bool) (j : ℕ) :
    R.classicalHalfPeriodCharacter b j ≃ₗ[ℂ] hemisphereWeakRadical k j b :=
  (R.classicalHalfPeriodRadicalEquiv b j).trans (hemisphereRadicalEquiv k j b)

theorem classical_halfPeriod_hemisphere_nullity (R : PaperHalfPeriodRealization k)
    (b : Bool) (j : ℕ) :
    Module.finrank ℂ (R.classicalHalfPeriodCharacter b j) =
      Module.finrank ℂ (hemisphereWeakRadical k j b) :=
  (R.classicalHalfPeriodHemisphereEquiv b j).finrank_eq

lemma classicalHalfPeriodCharacter_finiteDimensional (R : PaperHalfPeriodRealization k)
    (b : Bool) (j : ℕ) : FiniteDimensional ℂ (R.classicalHalfPeriodCharacter b j) := by
  let := hemisphereWeakRadical_finiteDimensional k j b
  exact (R.classicalHalfPeriodHemisphereEquiv b j).symm.finiteDimensional

end KsIndex.KarcherData.PaperHalfPeriodRealization
