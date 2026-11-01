module

public import KsIndexLean.SmoothDiskGreen
public import KsIndexLean.NaturalCoreCharacter
public import KsIndexLean.SlitReflectionDecomposition
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- A smooth, nonnegative test vanishing on arc1, invariant under every cube
root of unity, and strictly positive in arc0. No endpoint cutoff limit is used. -/
def slitFluxTestReal (w : ℂ) : ℝ := expNegInvGlue (-(w ^ 3).re)
def slitFluxTest (w : ℂ) : ℂ := slitFluxTestReal w

lemma slitFluxTestReal_smooth : ContDiff ℝ ∞ slitFluxTestReal :=
  expNegInvGlue.contDiff.comp ((Complex.reCLM.contDiff.comp (contDiff_id.pow 3)).neg)

lemma slitFluxTest_smooth : ContDiff ℝ ∞ slitFluxTest :=
  Complex.ofRealCLM.contDiff.comp slitFluxTestReal_smooth

lemma slitFluxTest_rotation {a : ℂ} (ha : a ^ 3 = 1) (w : ℂ) :
    slitFluxTest (a * w) = slitFluxTest w := by
  simp only [slitFluxTest, slitFluxTestReal, mul_pow, ha, one_mul]

lemma slitFluxTest_arc1_zero {w : Circle₁} (hw : w ∈ boundaryArc 3 1) :
    slitFluxTest w = 0 := by
  have hh := (mem_boundaryArc 3 1 w).mp hw
  have hp : 0 < ((w : ℂ) ^ 3).re := by simpa using hh
  simp only [slitFluxTest, slitFluxTestReal,
    expNegInvGlue.zero_of_nonpos (neg_nonpos.mpr hp.le), Complex.ofReal_zero]

lemma slitFluxTest_boundary_integral_pos :
    0 < ∫ w : Circle₁, slitFluxTestReal w ∂circleMeasure := by
  have hc : Continuous (fun w : Circle₁ => slitFluxTestReal w) :=
    slitFluxTestReal_smooth.continuous.comp continuous_subtype_val
  rw [integral_circleMeasure hc.aestronglyMeasurable,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.two_pi_pos.le]
  apply intervalIntegral.integral_pos Real.two_pi_pos
    (hc.comp continuous_circleParam).continuousOn
  · intro x _
    exact expNegInvGlue.nonneg _
  · refine ⟨Real.pi, ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩, ?_⟩
    change 0 < expNegInvGlue (-((circleParam Real.pi : ℂ) ^ 3).re)
    apply expNegInvGlue.pos_of_pos
    simp only [circleParam_coe, Complex.exp_pi_mul_I]
    norm_num [pow_succ, Complex.mul_re, Complex.mul_im]

lemma slitFluxTest_boundary_integral_ne_zero :
    (∫ w : Circle₁, slitFluxTest w ∂circleMeasure) ≠ 0 := by
  have hcast : (∫ w : Circle₁, slitFluxTest w ∂circleMeasure) =
      ((∫ w : Circle₁, slitFluxTestReal w ∂circleMeasure : ℝ) : ℂ) := by
    exact integral_ofReal
  rw [hcast]
  exact_mod_cast ne_of_gt slitFluxTest_boundary_integral_pos

def slitFluxTestH1 : ComplexH1 := globalSmoothH1 slitFluxTest slitFluxTest_smooth

lemma slitFluxTestH1_arc1_zero : slitFluxTestH1 ∈ zeroTraceDomain (boundaryArc 3 1) := by
  rw [mem_zeroTraceDomain]
  have h := (globalSmoothH1_trace slitFluxTest slitFluxTest_smooth).filter_mono
    (ae_mono (Measure.restrict_le_self (s := boundaryArc 3 1)))
  filter_upwards [h, ae_restrict_mem (measurableSet_boundaryArc 3 1)] with w hw ha
  exact hw.trans (slitFluxTest_arc1_zero ha)

lemma slitFluxTestH1_character_zero :
    slitFluxTestH1 ∈ weakCharacterDomain (-(2 * Real.pi) / 3) 1 := by
  apply weakCharacter_of_value_eq _ _ _ (globalSmoothH1_value _ _)
  intro z
  rw [one_mul, planeRotation_apply]
  apply slitFluxTest_rotation
  rw [← Complex.exp_nat_mul]
  have he : ((3 : ℕ) : ℂ) * (((-(2 * Real.pi) / 3 : ℝ) : ℂ) * Complex.I) =
      -(2 * Real.pi * Complex.I) := by push_cast; ring
  rw [he, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]

def slitFluxTestPair (phase : ℂ) : DiskPairH1 := (phase • slitFluxTestH1, slitFluxTestH1)

lemma slitFluxTestPair_mem_phase (phase : ℂ) :
    slitFluxTestPair phase ∈ slitTraceDomain 3 phase := by
  rw [mem_slitTraceDomain]
  have hz : arcTrace (boundaryArc 3 1) slitFluxTestH1 = 0 := slitFluxTestH1_arc1_zero
  constructor
  · change arcTrace _ (phase • slitFluxTestH1) = arcTrace _ slitFluxTestH1
    rw [map_smul, hz, smul_zero]
  · exact (arcTrace _).map_smul phase slitFluxTestH1

lemma slitFluxTestPair_mem_character_zero (phase : ℂ) :
    slitFluxTestPair phase ∈ pairCharacterDomain (-(2 * Real.pi) / 3) 1 := by
  rw [KsIndex.Spectral.mem_pairCharacterDomain_iff]
  exact ⟨(weakCharacterDomain _ _).smul_mem phase slitFluxTestH1_character_zero,
    slitFluxTestH1_character_zero⟩

lemma verticalThree_phase_test_pairing (phase : ℂ) :
    weakJacobi (surfacePotential 3) verticalThreeH1 (slitFluxTestPair phase).1 +
      weakJacobi (surfacePotential 3) (-verticalThreeH1) (slitFluxTestPair phase).2 =
        (phase - 1) * (2 * ∫ w : Circle₁, slitFluxTest w ∂circleMeasure) := by
  change weakJacobi _ _ (phase • slitFluxTestH1) + weakJacobi _ (-verticalThreeH1) slitFluxTestH1 = _
  rw [weakJacobi_smul_right, ← neg_one_smul ℂ verticalThreeH1, weakJacobi_smul_left]
  change phase * weakJacobi _ verticalThreeH1 (globalSmoothH1 slitFluxTest slitFluxTest_smooth) +
    (starRingEnd ℂ) (-1) * weakJacobi _ verticalThreeH1 (globalSmoothH1 slitFluxTest slitFluxTest_smooth) = _
  rw [verticalThree_smooth_green, map_neg, map_one]
  ring

lemma verticalThree_phase_test_pairing_ne_zero {phase : ℂ} (hp : phase ≠ 1) :
    weakJacobi (surfacePotential 3) verticalThreeH1 (slitFluxTestPair phase).1 +
      weakJacobi (surfacePotential 3) (-verticalThreeH1) (slitFluxTestPair phase).2 ≠ 0 := by
  rw [verticalThree_phase_test_pairing]
  exact mul_ne_zero (sub_ne_zero.mpr hp)
    (mul_ne_zero (by norm_num) slitFluxTest_boundary_integral_ne_zero)

/-- The vertical pair is not in the weak kernel at any nontrivial phase,
already on the actual character-zero test domain. Value traces alone would
not distinguish these phases; the concrete test detects the normal flux. -/
lemma verticalThree_not_phase_weak_kernel {phase : ℂ} (hp : phase ≠ 1) :
    ¬ (∀ v ∈ slitTraceDomain 3 phase ⊓ pairCharacterDomain (-(2 * Real.pi) / 3) 1,
      weakJacobi (surfacePotential 3) verticalThreeH1 v.1 +
        weakJacobi (surfacePotential 3) (-verticalThreeH1) v.2 = 0) := by
  intro h
  exact verticalThree_phase_test_pairing_ne_zero hp
    (h (slitFluxTestPair phase)
      ⟨slitFluxTestPair_mem_phase phase, slitFluxTestPair_mem_character_zero phase⟩)

lemma verticalThree_not_paper_weak_kernel (α : ℝ)
    (hp : Complex.exp ((2 * Real.pi * α) * Complex.I) ≠ 1) :
    ¬ (∀ v ∈ paperSlitCharacterDomain α 0,
      weakJacobi (surfacePotential 3) verticalThreeH1 v.1 +
        weakJacobi (surfacePotential 3) (-verticalThreeH1) v.2 = 0) := by
  simpa only [paperSlitCharacterDomain, paperSlitDomain, pow_zero] using
    verticalThree_not_phase_weak_kernel hp

end KsIndex.Trace
