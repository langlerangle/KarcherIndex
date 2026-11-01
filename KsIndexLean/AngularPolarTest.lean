module

public import KsIndexLean.AngularProfile

@[expose] public section


open Set MeasureTheory TopologicalSpace ContinuousLinearMap
open scoped Distributions ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

/-- Rotation derivative of an ambient angular test. -/
def angularTestDeriv (H : ℂ → ℝ) (z : ℂ) : ℝ := fderiv ℝ H z (z * Complex.I)

lemma contDiff_angularTestDeriv {H : ℂ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H) :
    ContDiff ℝ (⊤ : ℕ∞) (angularTestDeriv H) :=
  (contDiff_infty_iff_fderiv.mp hH).2.clm_apply (contDiff_id.mul contDiff_const)

lemma inner_rotation_zero (z : ℂ) : inner ℝ z (z * Complex.I) = 0 := by
  rw [real_inner_complex]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

lemma fderiv_nUnit_rotation {z : ℂ} (hz : z ≠ 0) :
    fderiv ℝ nUnit z (z * Complex.I) = nUnit z * Complex.I := by
  rw [(hasFDerivAt_nUnit hz).fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, smulRight_apply,
    innerSL_apply_apply, inner_rotation_zero, smul_eq_mul, mul_zero, zero_smul, add_zero]
  exact (smul_mul_assoc (‖z‖⁻¹) z Complex.I).symm

def polarTest (χ : ℝ → ℝ) (H : ℂ → ℝ) (z : ℂ) : ℝ := χ ‖z‖ * angExt H z

lemma contDiff_polarTest {a b : ℝ} (ha : 0 < a) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo a b)
    {H : ℂ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H) :
    ContDiff ℝ (⊤ : ℕ∞) (polarTest χ H) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) ha] with w hw
    have hn : ‖w‖ < a := by simpa [Metric.mem_ball, dist_zero_right] using hw
    have he : χ ‖w‖ = 0 := image_eq_zero_of_notMem_tsupport
      (fun hm => (not_lt.mpr hn.le) (hχs hm).1)
    simp only [polarTest, he, zero_mul]
  · have hn : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => ‖w‖) z := contDiffAt_norm ℝ hz
    have hu : ContDiffAt ℝ (⊤ : ℕ∞) nUnit z :=
      (hn.inv (norm_ne_zero_iff.mpr hz)).smul contDiffAt_id
    exact (hχ.contDiffAt.comp z hn).mul (hH.contDiffAt.comp z hu)

lemma tsupport_polarTest_subset {χ : ℝ → ℝ} {H : ℂ → ℝ} :
    tsupport (polarTest χ H) ⊆ (fun z : ℂ => ‖z‖) ⁻¹' tsupport χ := by
  apply closure_minimal _ (IsClosed.preimage continuous_norm isClosed_closure)
  intro z hz
  by_contra hn
  exact hz (by simp only [polarTest, image_eq_zero_of_notMem_tsupport hn, zero_mul])

lemma hasCompactSupport_polarTest {χ : ℝ → ℝ} (hc : HasCompactSupport χ) (H : ℂ → ℝ) :
    HasCompactSupport (polarTest χ H) := by
  obtain ⟨M, hM⟩ := hc.isBounded.subset_closedBall 0
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) M)
  intro z hz
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  have h := hM (tsupport_polarTest_subset hm)
  apply hz
  simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg z)] using h

lemma polarTest_rotation {a b : ℝ} (ha : 0 < a) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : tsupport χ ⊆ Ioo a b)
    {H : ℂ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H) (z : ℂ) :
    fderiv ℝ (polarTest χ H) z (z * Complex.I) = polarTest χ (angularTestDeriv H) z := by
  by_cases hz : z = 0
  · subst hz
    simp only [zero_mul, map_zero, polarTest, norm_zero, (phi_norm_zero_near_zero ha hχs).1]
  · have hc := (hχ.differentiable (by simp) ‖z‖).hasFDerivAt.comp z (hasFDerivAt_norm' hz)
    have hh := (hH.differentiable (by simp) (nUnit z)).hasFDerivAt.comp z
      (hasFDerivAt_nUnit hz)
    have hp := hc.mul hh
    change fderiv ℝ ((χ ∘ fun w : ℂ => ‖w‖) * (H ∘ nUnit)) z (z * Complex.I) = _
    rw [hp.fderiv]
    simp only [add_apply, smul_apply, comp_apply, innerSL_apply_apply,
      inner_rotation_zero, smul_eq_mul, mul_zero, map_zero, mul_zero, add_zero]
    have he := fderiv_nUnit_rotation hz
    rw [(hasFDerivAt_nUnit hz).fderiv] at he
    change χ ‖z‖ * _ = χ ‖z‖ * fderiv ℝ H (nUnit z) (nUnit z * Complex.I)
    congr 1
    apply congrArg (fderiv ℝ H (nUnit z))
    simpa only [add_apply, smul_apply] using he

end KsIndex.Trace
