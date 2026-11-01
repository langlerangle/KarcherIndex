module

public import KsIndexLean.KarcherDoubleSector

@[expose] public section


/-! Intrinsic rotations used to reduce ambient collisions to a fundamental wedge. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex Set
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma rotationLift_injective (R : PaperHalfPeriodRealization k) :
    Function.Injective R.rotationLift := by
  let θ : ℝ := -2 * Real.pi / k
  have hθ : Complex.exp ((θ : ℂ) * I) ^ (2 * k) = 1 := by
    rw [two_mul, pow_add, paper_rotation_root h.out, one_mul]
  have hinj : Function.Injective (parameterRotation θ hθ) := by
    apply Function.LeftInverse.injective (g := parameterRotation (-θ) (phase_root_neg hθ))
    intro p
    simpa using parameterRotation_neg_cancel (-θ) (phase_root_neg hθ) p
  intro q p he
  apply Subtype.ext
  apply Prod.ext
  · have hp := congrArg HeightLift.projection he
    rw [R.rotationLift_projection, R.rotationLift_projection] at hp
    exact hinj hp
  · change HeightLift.height q = HeightLift.height p
    have hh := congrArg HeightLift.height he
    simpa only [R.rotationLift_height] using hh

lemma rotationLift_collision (R : PaperHalfPeriodRealization k)
    {q p : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C}
    (he : centeredLiftAmbient R.C R.t q = centeredLiftAmbient R.C R.t p) :
    centeredLiftAmbient R.C R.t (R.rotationLift q) =
      centeredLiftAmbient R.C R.t (R.rotationLift p) := by
  rw [R.rotationLift_ambient, R.rotationLift_ambient, he]

lemma rotationIterate_collision (R : PaperHalfPeriodRealization k) (n : ℕ)
    {q p : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C}
    (he : centeredLiftAmbient R.C R.t q = centeredLiftAmbient R.C R.t p) :
    centeredLiftAmbient R.C R.t (R.rotationLift^[n] q) =
      centeredLiftAmbient R.C R.t (R.rotationLift^[n] p) := by
  induction n with
  | zero => exact he
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact R.rotationLift_collision ih

lemma rotationIterate_height (R : PaperHalfPeriodRealization k) (n : ℕ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    HeightLift.height (R.rotationLift^[n] q) = HeightLift.height q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', R.rotationLift_height, ih]

/-- Once the same intrinsic rotation puts both points in the proved wedge,
the original collision is resolved without any assumed ambient injectivity. -/
lemma collision_eq_of_rotated_doubleSector (R : PaperHalfPeriodRealization k) (n : ℕ)
    {q p : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C}
    (hq : R.rotationLift^[n] q ∈ R.doubleSector)
    (hp : R.rotationLift^[n] p ∈ R.doubleSector)
    (he : centeredLiftAmbient R.C R.t q = centeredLiftAmbient R.C R.t p) : q = p := by
  apply R.rotationLift_injective.iterate n
  exact R.doubleSector_injective hq hp (R.rotationIterate_collision n he)

lemma rotationIterate_finite (R : PaperHalfPeriodRealization k) (n : ℕ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) :
    ∃ v : PuncturedPlane k, HeightLift.projection (R.rotationLift^[n] q) = finiteParameter v ∧
      v.val = Complex.exp (((-2 * Real.pi / k : ℝ) : ℂ) * I) ^ n * w.val ∧
      ‖v.val‖ = ‖w.val‖ := by
  let a := Complex.exp (((-2 * Real.pi / k : ℝ) : ℂ) * I)
  have ha : a ^ (2 * k) = 1 := by
    rw [two_mul, pow_add, paper_rotation_root h.out, one_mul]
  induction n with
  | zero => exact ⟨w, hq, by simp, rfl⟩
  | succ n ih =>
    obtain ⟨v, hv, he, hn⟩ := ih
    let u : PuncturedPlane k := ⟨a * v.val, root_rotation_not_puncture ha v.property⟩
    refine ⟨u, ?_, ?_, ?_⟩
    · rw [Function.iterate_succ_apply', R.rotationLift_projection, hv]
      exact parameterRotation_finite _ _ v
    · change a * v.val = a ^ (n + 1) * w.val
      rw [he, pow_succ']
      ring
    · change ‖a * v.val‖ = ‖w.val‖
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, hn]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
