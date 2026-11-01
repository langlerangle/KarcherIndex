module

public import KsIndexLean.KarcherGlobalInjectivity
public import KsIndexLean.KarcherDoubleSectorEmbedding

@[expose] public section


/-! Continuous inverses for the symmetries used to assemble proper sectors. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open Set
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma rotationIterate_period (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.rotationLift^[k] q = q := by
  apply Subtype.ext
  apply Prod.ext
  · change HeightLift.projection (R.rotationLift^[k] q) = HeightLift.projection q
    rcases parameterSphere_cases (HeightLift.projection q) with hi | ⟨w, hw⟩
    · have step (n : ℕ) : HeightLift.projection (R.rotationLift^[n] q) = infinityParameter k := by
        induction n with
        | zero => exact hi
        | succ n ih => rw [Function.iterate_succ_apply', R.rotationLift_projection, ih,
            parameterRotation_infinity]
      exact (step k).trans hi.symm
    · obtain ⟨v, hv, he, _⟩ := R.rotationIterate_finite k q w hw.symm
      rw [hv, ← hw]
      congr 1
      apply Subtype.ext
      simpa only [paper_rotation_root h.out, one_mul] using he
  · exact R.rotationIterate_height k q

lemma rotationIterate_undo (R : PaperHalfPeriodRealization k) {n : ℕ} (hn : n ≤ k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.rotationLift^[k - n] (R.rotationLift^[n] q) = q := by
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hn, R.rotationIterate_period]

lemma screwLift_deck (R : PaperHalfPeriodRealization k) (n : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.screwLift (HeightLift.deck n q) = HeightLift.deck n (R.screwLift q) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (HeightLift.height q + (n : ℝ) * (2 * Real.pi)) + Real.pi =
      (HeightLift.height q + Real.pi) + (n : ℝ) * (2 * Real.pi)
    ring

/-- A continuous left inverse suffices for transporting compactness. -/
def screwLiftInverse (R : PaperHalfPeriodRealization k) :=
  fun q => R.rotationLift^[k - 1] (HeightLift.deck (-1) (R.screwLift q))

lemma screwLiftInverse_left (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.screwLiftInverse (R.screwLift q) = q := by
  change R.rotationLift^[k - 1] (R.rotationLift q) = q
  exact R.rotationIterate_undo (by have := h.out; omega) q

lemma continuous_screwLiftInverse (R : PaperHalfPeriodRealization k) :
    Continuous R.screwLiftInverse :=
  (R.continuous_rotationLift.iterate _).comp
    ((HeightLift.continuous_deck _).comp R.continuous_screwLift)

end KsIndex.KarcherData.PaperHalfPeriodRealization
