module

public import KsIndexLean.SlitVerticalExclusion

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- For k = 3, arc0 has positive arclength, witnessed by the smooth flux test. -/
lemma boundaryArc_three_zero_measure_pos : 0 < circleMeasure (boundaryArc 3 0) := by
  have hc : Continuous (fun w : Circle₁ => slitFluxTestReal w) :=
    slitFluxTestReal_smooth.continuous.comp continuous_subtype_val
  have hi : Integrable (fun w : Circle₁ => slitFluxTestReal w) circleMeasure :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp := (integral_pos_iff_support_of_nonneg
    (fun w : Circle₁ => expNegInvGlue.nonneg (-( (w : ℂ) ^ 3).re)) hi).mp
    slitFluxTest_boundary_integral_pos
  apply lt_of_lt_of_le hp
  apply measure_mono
  intro w hw
  rw [mem_boundaryArc]
  have hn : ¬ (-((w : ℂ) ^ 3).re ≤ 0) := by
    intro hz
    exact hw (expNegInvGlue.zero_of_nonpos hz)
  simpa using (neg_pos.mp (lt_of_not_ge hn))

lemma arcTrace_ne_zero_of_ae_nonzero (u : ComplexH1) (A : Set Circle₁)
    (hA : circleMeasure A ≠ 0)
    (hu : ∀ᵐ w ∂circleMeasure, (diskTraceCLM u : Circle₁ → ℂ) w ≠ 0) :
    arcTrace A u ≠ 0 := by
  intro hz
  have he : u ∈ zeroTraceDomain A := hz
  have he' := (mem_zeroTraceDomain A u).mp he
  have hn := hu.filter_mono (ae_mono (Measure.restrict_le_self (s := A)))
  have hf : ∀ᵐ w ∂circleMeasure.restrict A, False := by
    filter_upwards [he', hn] with w hw hne
    exact hne hw
  have hm := ae_iff.mp hf
  apply hA
  simpa using hm

lemma horizontalThree_arc0_trace_ne_zero :
    arcTrace (boundaryArc 3 0) horizontalThreeH1 ≠ 0 :=
  arcTrace_ne_zero_of_ae_nonzero _ _ (ne_of_gt boundaryArc_three_zero_measure_pos)
    horizontalThreeH1_trace_ne_zero_ae

/-- A repeated hemisphere field with nonzero slit trace can have only phase 1. -/
lemma diagonal_pair_phase_eq_one (u : ComplexH1) {phase : ℂ}
    (hu : arcTrace (boundaryArc 3 0) u ≠ 0)
    (hp : (u, u) ∈ slitTraceDomain 3 phase) : phase = 1 := by
  have he := ((mem_slitTraceDomain 3 phase (u, u)).mp hp).2
  have hz : (phase - 1) • arcTrace (boundaryArc 3 0) u = 0 := by
    rw [sub_smul, one_smul, ← he, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hu)

lemma horizontalThree_not_phase_domain {phase : ℂ} (hp : phase ≠ 1) :
    (horizontalThreeH1, horizontalThreeH1) ∉ slitTraceDomain 3 phase :=
  fun h => hp (diagonal_pair_phase_eq_one _ horizontalThree_arc0_trace_ne_zero h)

/-- Every scalar multiple of the horizontal repeated pair satisfying a
nontrivial slit phase relation is the zero multiple. -/
lemma horizontalThree_phase_scalar_zero {phase a : ℂ} (hp : phase ≠ 1)
    (h : (a • horizontalThreeH1, a • horizontalThreeH1) ∈ slitTraceDomain 3 phase) : a = 0 := by
  by_contra ha
  apply hp
  apply diagonal_pair_phase_eq_one _ _ h
  rw [map_smul]
  exact smul_ne_zero ha horizontalThree_arc0_trace_ne_zero

lemma horizontalThree_paper_scalar_zero {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {a : ℂ}
    (h : (a • horizontalThreeH1, a • horizontalThreeH1) ∈ paperSlitDomain α) : a = 0 :=
  horizontalThree_phase_scalar_zero (paperPhase_ne_one h0 h1) h

/-- The conjugate horizontal translation field, encoded independently as H1. -/
def horizontalThreeConjH1 : ComplexH1 := globalSmoothH1
  (fun w => (starRingEnd ℂ) (JacobiFields.nu1 3 w + Complex.I * JacobiFields.nu2 3 w))
  (Complex.conjCLE.contDiff.comp ((JacobiFields.nu1_contDiff 3 (by decide)).add
    (contDiff_const.mul (JacobiFields.nu2_contDiff 3 (by decide)))))

lemma horizontalThreeConjH1_trace :
    (diskTraceCLM horizontalThreeConjH1 : Circle₁ → ℂ) =ᵐ[circleMeasure]
      (fun w => (starRingEnd ℂ) ((w : ℂ) ^ 2)) := by
  have h := globalSmoothH1_trace
    (fun w => (starRingEnd ℂ) (JacobiFields.nu1 3 w + Complex.I * JacobiFields.nu2 3 w))
    (Complex.conjCLE.contDiff.comp ((JacobiFields.nu1_contDiff 3 (by decide)).add
      (contDiff_const.mul (JacobiFields.nu2_contDiff 3 (by decide)))))
  filter_upwards [h] with w hw
  exact hw.trans (congrArg (starRingEnd ℂ) (JacobiFields.horizontal_three_boundary
    (by simpa [Metric.mem_sphere, dist_zero_right] using w.property)))

lemma horizontalThreeConjH1_trace_ne_zero_ae :
    ∀ᵐ w ∂circleMeasure, (diskTraceCLM horizontalThreeConjH1 : Circle₁ → ℂ) w ≠ 0 := by
  filter_upwards [horizontalThreeConjH1_trace] with w hw
  rw [hw]
  have hn : ‖(w : ℂ)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using w.property
  have hz : (w : ℂ) ≠ 0 := by intro h; simp [h] at hn
  exact (map_ne_zero (starRingEnd ℂ)).mpr (pow_ne_zero 2 hz)

lemma horizontalThreeConj_arc0_trace_ne_zero :
    arcTrace (boundaryArc 3 0) horizontalThreeConjH1 ≠ 0 :=
  arcTrace_ne_zero_of_ae_nonzero _ _ (ne_of_gt boundaryArc_three_zero_measure_pos)
    horizontalThreeConjH1_trace_ne_zero_ae

lemma horizontalThreeConj_phase_scalar_zero {phase a : ℂ} (hp : phase ≠ 1)
    (h : (a • horizontalThreeConjH1, a • horizontalThreeConjH1) ∈ slitTraceDomain 3 phase) : a = 0 := by
  by_contra ha
  apply hp
  apply diagonal_pair_phase_eq_one _ _ h
  rw [map_smul]
  exact smul_ne_zero ha horizontalThreeConj_arc0_trace_ne_zero

lemma horizontalThreeConj_paper_scalar_zero {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {a : ℂ}
    (h : (a • horizontalThreeConjH1, a • horizontalThreeConjH1) ∈ paperSlitDomain α) : a = 0 :=
  horizontalThreeConj_phase_scalar_zero (paperPhase_ne_one h0 h1) h

end KsIndex.Trace
