module

public import KsIndexLean.KarcherTranslationPullback
public import KsIndexLean.KarcherRealSymmetries

@[expose] public section


/-! The height-preserving geometric rotation on finite period quotients. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma rotationLift_deck (R : PaperHalfPeriodRealization k) (j : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.rotationLift (HeightLift.deck j q) = HeightLift.deck j (R.rotationLift q) := by
  apply Subtype.ext
  apply Prod.ext
  · change HeightLift.projection _ = HeightLift.projection _
    simp only [rotationLift_projection, HeightLift.projection_deck]
  · change HeightLift.height _ = HeightLift.height _
    simp only [rotationLift_height, HeightLift.height_deck]

/-- Descend the actual height-preserving rotation, whose parameter angle is
`-2π/k`, to the quotient by `m` full periods. -/
def periodRotation (R : PaperHalfPeriodRealization k) (m : ℕ) :
    HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m →
      HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m :=
  Quotient.map R.rotationLift (by
    rintro q r ⟨j, rfl⟩
    exact ⟨j, (R.rotationLift_deck _ q).symm⟩)

@[simp] lemma periodRotation_mk (R : PaperHalfPeriodRealization k) (m : ℕ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.periodRotation m (HeightLift.periodQuotientMap m q) =
      HeightLift.periodQuotientMap m (R.rotationLift q) := rfl

lemma continuous_periodRotation (R : PaperHalfPeriodRealization k) (m : ℕ) :
    Continuous (R.periodRotation m) := by
  rw [(HeightLift.periodQuotientMap_isQuotientMap _).continuous_iff]
  exact (HeightLift.periodQuotientMap_isQuotientMap m).continuous.comp R.continuous_rotationLift

lemma periodRotation_deck (R : PaperHalfPeriodRealization k) (m : ℕ) (j : ℤ)
    (q : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :
    R.periodRotation m (HeightLift.periodDeck m j q) =
      HeightLift.periodDeck m j (R.periodRotation m q) := by
  induction q using Quotient.inductionOn with
  | h q => exact congrArg (HeightLift.periodQuotientMap m) (R.rotationLift_deck j q)

/-- Commuting geometric actions preserve translation eigenspaces. -/
lemma rotation_preserves_translation_eigenvalue (R : PaperHalfPeriodRealization k)
    (m : ℕ) (c : ℂ)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hf : ∀ q, f (HeightLift.periodDeck m 1 q) = c * f q) :
    ∀ q, (f ∘ R.periodRotation m) (HeightLift.periodDeck m 1 q) =
      c * (f ∘ R.periodRotation m) q := by
  intro q
  simp only [Function.comp_apply, R.periodRotation_deck]
  exact hf _

end KsIndex.KarcherData.PaperHalfPeriodRealization
