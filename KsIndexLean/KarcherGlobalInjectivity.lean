module

public import KsIndexLean.KarcherUpperHalfSlabInjectivity

@[expose] public section


/-! Injectivity of the actual normalized singly periodic EW immersion. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open Set
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma screwLift_injective (R : PaperHalfPeriodRealization k) :
    Function.Injective R.screwLift := by
  intro q p he
  apply R.rotationLift_injective
  unfold rotationLift
  rw [he]

lemma halfSlab_injective (R : PaperHalfPeriodRealization k)
    (q p : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.height q + Real.pi ∈ Icc 0 Real.pi)
    (hp : HeightLift.height p + Real.pi ∈ Icc 0 Real.pi)
    (he : centeredLiftAmbient R.C R.t q = centeredLiftAmbient R.C R.t p) : q = p := by
  have hh := congrArg (fun v : AmbientTriple => v.2.2) he
  change HeightLift.height q + Real.pi = HeightLift.height p + Real.pi at hh
  by_cases hz : Real.pi / 2 ≤ HeightLift.height q + Real.pi
  · exact R.upperHalfSlab_injective q p ⟨hz, hq.2⟩ ⟨by linarith, hp.2⟩ he
  let f := fun q => R.screwLift (lowerSeamLift R.C R.hC q)
  have hheight (r : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
      HeightLift.height (f r) + Real.pi = Real.pi - (HeightLift.height r + Real.pi) := by
    dsimp [f]
    rw [R.screwLift_height]
    have ht := lowerSeamLift_height R.C R.hC r
    linarith
  have he' : centeredLiftAmbient R.C R.t (f q) = centeredLiftAmbient R.C R.t (f p) := by
    dsimp [f]
    rw [R.screwLift_ambient, R.screwLift_ambient,
      centeredLiftAmbient_lowerSeam, centeredLiftAmbient_lowerSeam, he]
  have hsame : f q = f p := by
    apply R.upperHalfSlab_injective _ _ _ _ he'
    · rw [hheight]
      constructor <;> linarith [hq.1]
    · rw [hheight]
      constructor <;> linarith [hp.1]
  exact (lowerSeamLift_involutive R.C R.hC).injective (R.screwLift_injective hsame)

lemma periodSlab_injective (R : PaperHalfPeriodRealization k)
    (q p : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.height q + Real.pi ∈ Icc 0 (2 * Real.pi))
    (hp : HeightLift.height p + Real.pi ∈ Icc 0 (2 * Real.pi))
    (he : centeredLiftAmbient R.C R.t q = centeredLiftAmbient R.C R.t p) : q = p := by
  have hh := congrArg (fun v : AmbientTriple => v.2.2) he
  change HeightLift.height q + Real.pi = HeightLift.height p + Real.pi at hh
  by_cases hz : HeightLift.height q + Real.pi ≤ Real.pi
  · exact R.halfSlab_injective q p ⟨hq.1, hz⟩ ⟨hp.1, by linarith⟩ he
  apply (upperSeamLift_involutive R.C R.hC).injective
  apply R.halfSlab_injective
  · rw [upperSeamLift_height]
    constructor <;> linarith [hq.2]
  · rw [upperSeamLift_height]
    constructor <;> linarith [hp.2]
  · rw [centeredLiftAmbient_upperSeam, centeredLiftAmbient_upperSeam, he]

lemma centeredAmbient_deck (R : PaperHalfPeriodRealization k) (n : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    centeredLiftAmbient R.C R.t (HeightLift.deck n q) =
      ((centeredLiftAmbient R.C R.t q).1, (centeredLiftAmbient R.C R.t q).2.1,
        (centeredLiftAmbient R.C R.t q).2.2 + (n : ℝ) * (2 * Real.pi)) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · change HeightLift.height q + (n : ℝ) * (2 * Real.pi) + Real.pi = _
      change _ = HeightLift.height q + Real.pi + (n : ℝ) * (2 * Real.pi)
      ring

/-- No two distinct intrinsic points have the same actual Euclidean position. -/
theorem centeredLiftAmbient_injective (R : PaperHalfPeriodRealization k) :
    Function.Injective (centeredLiftAmbient (k := k) R.C R.t) := by
  intro q p he
  let z := HeightLift.height q + Real.pi
  let j : ℤ := ⌊z / (2 * Real.pi)⌋
  have hpi : 0 < 2 * Real.pi := by positivity
  have hlo := (le_div_iff₀ hpi).mp (Int.floor_le (z / (2 * Real.pi)))
  have hhi := (div_lt_iff₀ hpi).mp (Int.lt_floor_add_one (z / (2 * Real.pi)))
  change (j : ℝ) * (2 * Real.pi) ≤ z at hlo
  change z < ((j : ℝ) + 1) * (2 * Real.pi) at hhi
  have hq : HeightLift.height (HeightLift.deck (-j) q) + Real.pi ∈ Icc 0 (2 * Real.pi) := by
    rw [HeightLift.height_deck]
    push_cast
    change 0 ≤ HeightLift.height q + -(j : ℝ) * (2 * Real.pi) + Real.pi ∧ _
    dsimp [z] at hlo hhi
    constructor <;> nlinarith
  have hh := congrArg (fun v : AmbientTriple => v.2.2) he
  change HeightLift.height q + Real.pi = HeightLift.height p + Real.pi at hh
  have hp : HeightLift.height (HeightLift.deck (-j) p) + Real.pi ∈ Icc 0 (2 * Real.pi) := by
    rw [HeightLift.height_deck] at hq ⊢
    constructor <;> linarith [hq.1, hq.2]
  have he' : centeredLiftAmbient R.C R.t (HeightLift.deck (-j) q) =
      centeredLiftAmbient R.C R.t (HeightLift.deck (-j) p) := by
    rw [R.centeredAmbient_deck, R.centeredAmbient_deck, he]
  have hs := R.periodSlab_injective _ _ hq hp he'
  have ht := congrArg (HeightLift.deck j) hs
  simpa only [← HeightLift.deck_add, add_neg_cancel, HeightLift.deck_zero] using ht

end KsIndex.KarcherData.PaperHalfPeriodRealization
