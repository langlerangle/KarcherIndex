module

public import KsIndexLean.KarcherTranslationPullback
public import KsIndexLean.KarcherRealConjugation

@[expose] public section


/-! The geometric reflection in y=0 on finite period quotients. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma conjugationLift_deck (R : PaperHalfPeriodRealization k) (j : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.conjugationLift (HeightLift.deck j q) = HeightLift.deck j (R.conjugationLift q) := by
  apply Subtype.ext
  apply Prod.ext
  · change HeightLift.projection _ = HeightLift.projection _
    simp only [conjugationLift_projection, HeightLift.projection_deck]
  · change HeightLift.height _ = HeightLift.height _
    simp only [conjugationLift_height, HeightLift.height_deck]

/-- Descend the actual height-preserving reflection in y=0 to the quotient
by `m` full periods. -/
def periodConjugation (R : PaperHalfPeriodRealization k) (m : ℕ) :
    HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m →
      HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m :=
  Quotient.map R.conjugationLift (by
    rintro q r ⟨j, rfl⟩
    exact ⟨j, (R.conjugationLift_deck _ q).symm⟩)

@[simp] lemma periodConjugation_mk (R : PaperHalfPeriodRealization k) (m : ℕ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.periodConjugation m (HeightLift.periodQuotientMap m q) =
      HeightLift.periodQuotientMap m (R.conjugationLift q) := rfl

lemma continuous_periodConjugation (R : PaperHalfPeriodRealization k) (m : ℕ) :
    Continuous (R.periodConjugation m) := by
  rw [(HeightLift.periodQuotientMap_isQuotientMap _).continuous_iff]
  exact (HeightLift.periodQuotientMap_isQuotientMap m).continuous.comp R.continuous_conjugationLift

lemma periodConjugation_deck (R : PaperHalfPeriodRealization k) (m : ℕ) (j : ℤ)
    (q : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :
    R.periodConjugation m (HeightLift.periodDeck m j q) =
      HeightLift.periodDeck m j (R.periodConjugation m q) := by
  induction q using Quotient.inductionOn with
  | h q => exact congrArg (HeightLift.periodQuotientMap m) (R.conjugationLift_deck j q)

/-- Commuting geometric actions preserve translation eigenspaces. -/
lemma conjugation_preserves_translation_eigenvalue (R : PaperHalfPeriodRealization k)
    (m : ℕ) (c : ℂ)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hf : ∀ q, f (HeightLift.periodDeck m 1 q) = c * f q) :
    ∀ q, (f ∘ R.periodConjugation m) (HeightLift.periodDeck m 1 q) =
      c * (f ∘ R.periodConjugation m) q := by
  intro q
  simp only [Function.comp_apply, R.periodConjugation_deck]
  exact hf _

end KsIndex.KarcherData.PaperHalfPeriodRealization
