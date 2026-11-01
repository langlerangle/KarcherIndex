module

public import KsIndexLean.GeneralDirichletValues
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

@[expose] public section


/-!
# Slit flux tests and injectivity of the Neumann trace

A smooth nonnegative test has nonzero circle integral. Its Green pairing
with the radial Dirichlet witness has constant flux `−κ²`, which proves
`weak_neumann_zero_of_trace_zero_gen`: a full weak solution with zero trace
vanishes. `GeneralNeumannRow` uses this trace injectivity to bound nullity.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.ModeDiag KsIndex.Radial KsIndex.JacobiMode

variable {k : ℕ}

/-- The general slit flux test: smooth, nonnegative, supported off the closed
`arc 1` side, strictly positive inside `arc 0`. -/
def slitFluxTestKReal (k : ℕ) (w : ℂ) : ℝ := expNegInvGlue (-(w ^ k).re)
def slitFluxTestK (k : ℕ) (w : ℂ) : ℂ := slitFluxTestKReal k w

lemma slitFluxTestKReal_smooth (k : ℕ) : ContDiff ℝ ∞ (slitFluxTestKReal k) :=
  expNegInvGlue.contDiff.comp ((Complex.reCLM.contDiff.comp (contDiff_id.pow k)).neg)

lemma slitFluxTestK_smooth (k : ℕ) : ContDiff ℝ ∞ (slitFluxTestK k) :=
  Complex.ofRealCLM.contDiff.comp (slitFluxTestKReal_smooth k)

lemma slitFluxTestK_boundary_integral_pos (hk : 1 ≤ k) :
    0 < ∫ w : Circle₁, slitFluxTestKReal k w ∂circleMeasure := by
  have hc : Continuous (fun w : Circle₁ => slitFluxTestKReal k w) :=
    (slitFluxTestKReal_smooth k).continuous.comp continuous_subtype_val
  rw [integral_circleMeasure hc.aestronglyMeasurable,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.two_pi_pos.le]
  apply intervalIntegral.integral_pos Real.two_pi_pos
    (hc.comp continuous_circleParam).continuousOn
  · intro x _
    exact expNegInvGlue.nonneg _
  · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    refine ⟨Real.pi / k, ⟨by positivity, ?_⟩, ?_⟩
    · have hd : Real.pi / k ≤ Real.pi := div_le_self Real.pi_pos.le hkR
      linarith [Real.pi_pos]
    · change 0 < expNegInvGlue (-((circleParam (Real.pi / k) : ℂ) ^ k).re)
      apply expNegInvGlue.pos_of_pos
      rw [circleParam_coe, ← Complex.exp_nat_mul]
      have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      have he : (k : ℂ) * (((Real.pi / k : ℝ) : ℂ) * Complex.I) =
          Real.pi * Complex.I := by
        push_cast
        field_simp
      rw [he, Complex.exp_pi_mul_I]
      norm_num

lemma slitFluxTestK_boundary_integral_ne_zero (hk : 1 ≤ k) :
    (∫ w : Circle₁, slitFluxTestK k w ∂circleMeasure) ≠ 0 := by
  have hcast : (∫ w : Circle₁, slitFluxTestK k w ∂circleMeasure) =
      ((∫ w : Circle₁, slitFluxTestKReal k w ∂circleMeasure : ℝ) : ℂ) :=
    integral_ofReal
  rw [hcast]
  exact_mod_cast ne_of_gt (slitFluxTestK_boundary_integral_pos hk)

def slitFluxTestKH1 (k : ℕ) : ComplexH1 :=
  globalSmoothH1 (slitFluxTestK k) (slitFluxTestK_smooth k)

/-- The radial Dirichlet witness pairs with EVERY weak test through its
constant boundary flux `−κ²` (the 812 route, extracted). -/
lemma radialDirichlet_weak_green (hk : 2 ≤ k) (v : ComplexH1) :
    weakJacobi (surfacePotential k) (radialDirichletH1 hk) v =
      -(((kap k : ℝ) ^ 2 : ℝ) : ℂ) *
        ∫ w : Circle₁, (diskTraceCLM v : Circle₁ → ℂ) w ∂circleMeasure := by
  let a : ℂ := -(((kap k : ℝ) ^ 2 : ℝ) : ℂ)
  have hF : ((a • circleOneL2 : Lp ℂ 2 circleMeasure) : Circle₁ → ℂ)
      =ᵐ[circleMeasure] fun w => fderiv ℝ (modeU k 0) w w := by
    filter_upwards [Lp.coeFn_smul a circleOneL2,
      (MemLp.coeFn_toLp (memLp_const (1 : ℂ)))] with w hw ho
    rw [hw]
    change a * circleOneL2 w = _
    change circleOneL2 w = 1 at ho
    have hw1 : ‖(w : ℂ)‖ = 1 := by
      simpa only [Circle₁, Metric.mem_sphere, dist_zero_right] using w.property
    rw [ho, mul_one, modeU_normal hk 0 hw1]
    simp [a]
  rw [show weakJacobi (surfacePotential k) (radialDirichletH1 hk) v =
      inner ℂ (a • circleOneL2) (diskTraceCLM v) from
    smooth_weak_green_of_flux _ _ (modeU_contDiff (by omega) 0)
      (fun w _ => modeU_jacobi hk 0 w) _ hF v]
  rw [inner_smul_left, L2.inner_def]
  have hone : ∀ᵐ w ∂circleMeasure, (circleOneL2 : Circle₁ → ℂ) w = 1 :=
    MemLp.coeFn_toLp (memLp_const (1 : ℂ))
  have hint : (∫ w : Circle₁, (diskTraceCLM v : Circle₁ → ℂ) w *
      (starRingEnd ℂ) ((circleOneL2 : Circle₁ → ℂ) w) ∂circleMeasure) =
      ∫ w : Circle₁, (diskTraceCLM v : Circle₁ → ℂ) w ∂circleMeasure := by
    apply integral_congr_ae
    filter_upwards [hone] with w hw
    rw [hw, map_one, mul_one]
  simp only [RCLike.inner_apply]
  rw [hint]
  congr 1
  simp [a]

lemma radialDirichlet_fluxTest_pairing_ne_zero (hk : 2 ≤ k) :
    weakJacobi (surfacePotential k) (radialDirichletH1 hk) (slitFluxTestKH1 k) ≠ 0 := by
  rw [radialDirichlet_weak_green hk]
  apply mul_ne_zero
  · simp only [neg_ne_zero, Complex.ofReal_ne_zero]
    exact pow_ne_zero 2 (ne_of_gt (kap_pos hk))
  · have ht : (∫ w : Circle₁, (diskTraceCLM (slitFluxTestKH1 k) : Circle₁ → ℂ) w
        ∂circleMeasure) = ∫ w : Circle₁, slitFluxTestK k w ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [globalSmoothH1_trace (slitFluxTestK k) (slitFluxTestK_smooth k)]
        with w hw
      exact hw
    rw [ht]
    exact slitFluxTestK_boundary_integral_ne_zero (by omega)

/-- **V3 headline**: a full weak Jacobi solution with zero boundary trace is zero,
at every `k ≥ 2` — the Neumann trace-injectivity. -/
theorem weak_neumann_zero_of_trace_zero_gen (hk : 2 ≤ k) (u : ComplexH1)
    (hu : ∀ v : ComplexH1, weakJacobi (surfacePotential k) u v = 0)
    (ht : diskTraceCLM u = 0) : u = 0 := by
  obtain ⟨c, hc⟩ := generalDirichlet_kernel_span hk u
    ((mem_fullZeroTrace_iff u).mpr ht) (fun v _ => hu v)
  have h := hu (slitFluxTestKH1 k)
  rw [hc, weakJacobi_smul_left] at h
  have hz := (mul_eq_zero.mp h).resolve_right
    (radialDirichlet_fluxTest_pairing_ne_zero hk)
  have hc0 : c = 0 := (starRingEnd ℂ).injective
    (hz.trans (map_zero (starRingEnd ℂ)).symm)
  rw [hc, hc0, zero_smul]

end KsIndex.Trace
