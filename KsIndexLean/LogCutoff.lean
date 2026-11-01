module

/-
# Logarithmic cutoffs for puncture removal

For `0 < ε < 1` and a center `z₀`,

  `logCutoff ε z₀ z = smoothTransition (log (‖z−z₀‖/ε²) / (−log ε))`

is smooth on all of `ℂ`, takes values in `[0,1]`, vanishes on the closed
ball of radius `ε²`, and equals `1` at distance at least `ε`. At the center,
Lean's value `Real.log 0 = 0` places the profile at zero; smoothness follows
from local constancy on the inner ball.

The module also proves the derivative and energy bounds. If `C` bounds
`|deriv Real.smoothTransition|`, then the derivative operator norm is at most
`C/(‖z−z₀‖·(−log ε))` away from the center, and
`∫ z, ‖fderiv ℝ (logCutoff ε z₀) z‖² ≤ 2πC²/(−log ε)`.
The latter follows by integrating a radial majorant on the closed transition
annulus. It supplies the vanishing-energy estimate used by `PunctureRemoval`.
-/
public import KsIndexLean.WeakH1Adapter
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section


noncomputable section
open MeasureTheory
namespace KsIndex.LogCutoff

/-- For `0 < ε < 1`, the logarithmic cutoff is `0` on `‖z−z₀‖ ≤ ε²`, `1` off `‖z−z₀‖ < ε`,
smoothly interpolated in between at logarithmic rate. -/
def logCutoff (ε : ℝ) (z₀ : ℂ) (z : ℂ) : ℝ :=
  Real.smoothTransition (Real.log (‖z - z₀‖ / ε ^ 2) / (-Real.log ε))

variable {ε : ℝ} (z₀ : ℂ)

lemma logCutoff_nonneg (z : ℂ) : 0 ≤ logCutoff ε z₀ z :=
  Real.smoothTransition.nonneg _

lemma logCutoff_le_one (z : ℂ) : logCutoff ε z₀ z ≤ 1 :=
  Real.smoothTransition.le_one _

/-- The cutoff vanishes on the closed inner ball (center included: `log 0 = 0`
puts the profile at `0` and `smoothTransition 0 = 0`). -/
lemma logCutoff_eq_zero (hε : 0 < ε) (hε1 : ε < 1) {z : ℂ}
    (h : ‖z - z₀‖ ≤ ε ^ 2) : logCutoff ε z₀ z = 0 := by
  have hlog : Real.log ε < 0 := Real.log_neg hε hε1
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg
  · exact Real.log_nonpos (by positivity)
      ((div_le_one (by positivity)).mpr h)
  · linarith

/-- The cutoff equals `1` outside the ball of radius `ε`. -/
lemma logCutoff_eq_one (hε : 0 < ε) (hε1 : ε < 1) {z : ℂ}
    (h : ε ≤ ‖z - z₀‖) : logCutoff ε z₀ z = 1 := by
  have hlog : Real.log ε < 0 := Real.log_neg hε hε1
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by linarith)]
  have h1 : (0 : ℝ) < ε / ε ^ 2 := by positivity
  have h2 : Real.log (ε / ε ^ 2) ≤ Real.log (‖z - z₀‖ / ε ^ 2) :=
    Real.log_le_log h1 (by
      apply div_le_div_of_nonneg_right h (by positivity))
  have h3 : Real.log (ε / ε ^ 2) = -Real.log ε := by
    rw [Real.log_div (ne_of_gt hε) (by positivity), Real.log_pow]
    push_cast
    ring
  linarith

/-- The cutoff is identically zero on a neighborhood of the center. -/
lemma logCutoff_eventually_zero (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ z in nhds z₀, logCutoff ε z₀ z = 0 := by
  filter_upwards [Metric.ball_mem_nhds z₀ (show (0:ℝ) < ε ^ 2 by positivity)]
    with z hz
  refine logCutoff_eq_zero z₀ hε hε1 (le_of_lt ?_)
  simpa [dist_eq_norm] using Metric.mem_ball.mp hz

/-- **Smoothness.**  The log-cutoff is `C^∞` on all of `ℂ`: near the center it
is locally the constant `0`; away from the center it is a composite of smooth
maps (`smoothTransition ∘ (affine) ∘ log ∘ (‖·‖/ε²)` with positive argument). -/
lemma contDiff_logCutoff (hε : 0 < ε) (hε1 : ε < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (logCutoff ε z₀) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = z₀
  · subst hz
    exact contDiffAt_const.congr_of_eventuallyEq
      (logCutoff_eventually_zero z hε hε1)
  · have hne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
    have hnorm : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => ‖w - z₀‖) z := by
      exact (contDiffAt_norm ℂ hne).comp z
        ((contDiff_id.sub contDiff_const).contDiffAt)
    have hpos : ‖z - z₀‖ / ε ^ 2 > 0 := by
      have := norm_pos_iff.mpr hne
      positivity
    have harg : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun w : ℂ => Real.log (‖w - z₀‖ / ε ^ 2) / (-Real.log ε)) z := by
      apply ContDiffAt.div_const
      exact (Real.contDiffAt_log.mpr (ne_of_gt hpos)).comp z (hnorm.div_const _)
    exact Real.smoothTransition.contDiffAt.comp z harg

/-! ### The gradient bound

The cutoff is the radial profile `g(t) = smoothTransition (log (t/ε²) / (−log ε))`
composed with the 1-Lipschitz map `w ↦ ‖w − z₀‖`, so the gradient estimate is a
one-variable chain rule: `‖∇(logCutoff ε z₀)(z)‖ ≤ C/(‖z−z₀‖·(−log ε))` for every
`z ≠ z₀`, where `C` bounds `|deriv smoothTransition|` (finite: continuous on the
compact `[−1,2]`, zero outside by local constancy).  Inside the open inner ball and outside the closed outer ball, the gradient
vanishes by local constancy. Together these bounds give a majorant supported
on the closed transition annulus, including both boundary circles. -/

/-- `|deriv smoothTransition|` is globally bounded. -/
lemma exists_transition_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 2
  · exact le_trans (by simpa using hC x hx) (le_max_left _ _)
  · have hzero : deriv Real.smoothTransition x = 0 := by
      rcases not_and_or.mp hx with h | h
      · push Not at h
        have hev : Real.smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ) := by
          filter_upwards [Iio_mem_nhds (show x < 0 by linarith)] with y hy
          exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
        rw [hev.deriv_eq, deriv_const]
      · push Not at h
        have hev : Real.smoothTransition =ᶠ[nhds x] fun _ => (1 : ℝ) := by
          filter_upwards [Ioi_mem_nhds (show 1 < x by linarith)] with y hy
          exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
        rw [hev.deriv_eq, deriv_const]
    rw [hzero]
    simp [le_max_iff]

/-- The distance-to-center map is 1-Lipschitz. -/
lemma lipschitz_normSub (z₀ : ℂ) : LipschitzWith 1 (fun w : ℂ => ‖w - z₀‖) := by
  have h1 : LipschitzWith 1 (fun w : ℂ => w - z₀) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      simp only [dist_eq_norm, NNReal.coe_one, one_mul]
      exact le_of_eq (by ring_nf)
  simpa [Function.comp_def] using lipschitzWith_one_norm.comp h1

/-- **The pointwise gradient bound** (every `z ≠ z₀`): the chain rule through
the radial profile, with the Lipschitz bound `‖∇‖·−z₀‖‖ ≤ 1`. -/
lemma norm_fderiv_logCutoff_le (hε : 0 < ε) (hε1 : ε < 1)
    {C : ℝ} (hC : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C)
    {z : ℂ} (hz : z ≠ z₀) :
    ‖fderiv ℝ (logCutoff ε z₀) z‖ ≤ C / (‖z - z₀‖ * (-Real.log ε)) := by
  have hlog : Real.log ε < 0 := Real.log_neg hε hε1
  have hr : (0 : ℝ) < ‖z - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  -- the radial profile and its derivative at r := ‖z − z₀‖
  set r := ‖z - z₀‖ with hrdef
  have hinner : HasDerivAt (fun t : ℝ => Real.log (t / ε ^ 2)) (1 / r) r := by
    have h1 : HasDerivAt (fun t : ℝ => t / ε ^ 2) (1 / ε ^ 2) r := by
      simpa using (hasDerivAt_id r).div_const (ε ^ 2)
    have h2 := (Real.hasDerivAt_log (by positivity : r / ε ^ 2 ≠ 0)).comp r h1
    have hval : (r / ε ^ 2)⁻¹ * (1 / ε ^ 2) = 1 / r := by
      field_simp [hr.ne', hε.ne']
    exact hval ▸ h2
  have hprof : HasDerivAt
      (fun t : ℝ => Real.smoothTransition (Real.log (t / ε ^ 2) / (-Real.log ε)))
      (deriv Real.smoothTransition (Real.log (r / ε ^ 2) / (-Real.log ε))
        * (1 / r / (-Real.log ε))) r := by
    have hη : HasDerivAt Real.smoothTransition
        (deriv Real.smoothTransition (Real.log (r / ε ^ 2) / (-Real.log ε)))
        (Real.log (r / ε ^ 2) / (-Real.log ε)) :=
      ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable
        (by simp)).differentiableAt.hasDerivAt
    exact hη.comp r (hinner.div_const _)
  -- the distance map: differentiable with ‖derivative‖ ≤ 1
  have hnormAt : HasFDerivAt (fun w : ℂ => ‖w - z₀‖)
      (fderiv ℝ (fun w : ℂ => ‖w - z₀‖) z) z := by
    have : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => ‖w - z₀‖) z :=
      (contDiffAt_norm ℂ (sub_ne_zero.mpr hz)).comp z
        ((contDiff_id.sub contDiff_const).contDiffAt)
    exact (this.differentiableAt (by simp)).hasFDerivAt
  have hD1 : ‖fderiv ℝ (fun w : ℂ => ‖w - z₀‖) z‖ ≤ 1 := by
    simpa using hnormAt.le_of_lipschitz (lipschitz_normSub z₀)
  -- compose: logCutoff = profile ∘ distance, literally
  have hcomp := hprof.comp_hasFDerivAt (x := z) hnormAt
  have hfd : fderiv ℝ (logCutoff ε z₀) z
      = (deriv Real.smoothTransition (Real.log (r / ε ^ 2) / (-Real.log ε))
          * (1 / r / (-Real.log ε))) • fderiv ℝ (fun w : ℂ => ‖w - z₀‖) z :=
    hcomp.fderiv
  rw [hfd, norm_smul]
  calc ‖deriv Real.smoothTransition (Real.log (r / ε ^ 2) / (-Real.log ε))
        * (1 / r / (-Real.log ε))‖ * ‖fderiv ℝ (fun w : ℂ => ‖w - z₀‖) z‖
      ≤ ‖deriv Real.smoothTransition (Real.log (r / ε ^ 2) / (-Real.log ε))
        * (1 / r / (-Real.log ε))‖ * 1 := by
        apply mul_le_mul_of_nonneg_left hD1 (norm_nonneg _)
    _ ≤ C / (r * (-Real.log ε)) := by
        have hc : (0 : ℝ) < -Real.log ε := by linarith
        rw [mul_one, Real.norm_eq_abs, abs_mul]
        have h1 : |1 / r / (-Real.log ε)| = 1 / (r * (-Real.log ε)) := by
          rw [abs_of_pos (div_pos (div_pos one_pos hr) hc)]
          field_simp
        rw [h1]
        rw [div_eq_mul_one_div C (r * (-Real.log ε))]
        exact mul_le_mul_of_nonneg_right (hC _)
          (le_of_lt (one_div_pos.mpr (mul_pos hr hc)))

/-- The gradient VANISHES on the open inner ball (center included). -/
lemma fderiv_logCutoff_inner (hε : 0 < ε) (hε1 : ε < 1) {z : ℂ}
    (h : ‖z - z₀‖ < ε ^ 2) : fderiv ℝ (logCutoff ε z₀) z = 0 := by
  have hev : logCutoff ε z₀ =ᶠ[nhds z] fun _ => (0 : ℝ) := by
    have hopen : Metric.ball z₀ (ε ^ 2) ∈ nhds z :=
      Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_eq_norm] using h)
    filter_upwards [hopen] with w hw
    exact logCutoff_eq_zero z₀ hε hε1
      (le_of_lt (by simpa [dist_eq_norm] using Metric.mem_ball.mp hw))
  rw [hev.fderiv_eq]
  exact fderiv_const_apply 0

/-- The gradient VANISHES outside the closed outer ball. -/
lemma fderiv_logCutoff_outer (hε : 0 < ε) (hε1 : ε < 1) {z : ℂ}
    (h : ε < ‖z - z₀‖) : fderiv ℝ (logCutoff ε z₀) z = 0 := by
  have hev : logCutoff ε z₀ =ᶠ[nhds z] fun _ => (1 : ℝ) := by
    have hopen : {w : ℂ | ε < ‖w - z₀‖} ∈ nhds z := by
      have : IsOpen {w : ℂ | ε < ‖w - z₀‖} := by
        have : Continuous fun w : ℂ => ‖w - z₀‖ :=
          (continuous_id.sub continuous_const).norm
        exact isOpen_lt continuous_const this
      exact this.mem_nhds h
    filter_upwards [hopen] with w hw
    exact logCutoff_eq_one z₀ hε hε1 (le_of_lt hw)
  rw [hev.fderiv_eq]
  exact fderiv_const_apply 1

/-! ### The energy estimate (two-dimensional zero capacity)

`∫ ‖∇(logCutoff ε z₀)‖² ≤ 2π·C²/(−log ε) → 0`: the gradient is supported on the
transition annulus with the pointwise bound `C/(r·(−log ε))`, and the planar radial
integral `∫_{ε²≤r≤ε} r⁻² = 2π·(−log ε)` (polar/Haar-to-sphere) gives the claim. -/

open Set in
/-- The planar radial integral: `∫_ℂ 1_{ε²≤‖w‖≤ε}·‖w‖⁻² = 2π·(−log ε)`. -/
lemma integral_indicator_inv_sq_norm (hε : 0 < ε) (hε1 : ε < 1) :
    ∫ w : ℂ, indicator (Icc (ε ^ 2) ε) (fun t : ℝ => (t ^ 2)⁻¹) ‖w‖
      = 2 * Real.pi * (-Real.log ε) := by
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hlt : ε ^ 2 < ε := by nlinarith
  rw [MeasureTheory.integral_fun_norm_addHaar (volume : Measure ℂ)
    (indicator (Icc (ε ^ 2) ε) (fun t : ℝ => (t ^ 2)⁻¹))]
  rw [Complex.finrank_real_complex]
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [MeasureTheory.measureReal_def, Complex.volume_ball]
  rw [hball]
  have hcongr : ∀ y ∈ Set.Ioi (0 : ℝ),
      y ^ (2 - 1) • indicator (Icc (ε ^ 2) ε) (fun t : ℝ => (t ^ 2)⁻¹) y
        = indicator (Icc (ε ^ 2) ε) (fun t : ℝ => t⁻¹) y := by
    intro y _
    by_cases hmem : y ∈ Icc (ε ^ 2) ε
    · have hy0 : y ≠ 0 := ne_of_gt (lt_of_lt_of_le hε2 hmem.1)
      rw [indicator_of_mem hmem, indicator_of_mem hmem, smul_eq_mul,
        show (2 - 1 : ℕ) = 1 from rfl, pow_one,
        pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hy0, one_mul]
    · simp [indicator_of_notMem hmem]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Icc]
  have hcap : Set.Ioi (0 : ℝ) ∩ Icc (ε ^ 2) ε = Icc (ε ^ 2) ε :=
    inter_eq_right.mpr fun y hy => lt_of_lt_of_le hε2 hy.1
  rw [hcap, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (le_of_lt hlt),
    integral_inv_of_pos hε2 hε]
  rw [Real.log_div (ne_of_gt hε) (ne_of_gt hε2), Real.log_pow]
  push_cast
  have : Real.log ε - 2 * Real.log ε = -Real.log ε := by ring
  rw [this]
  simp [smul_eq_mul]
  ring

open Set in
/-- **The energy estimate** (the 2D zero-capacity fact): the Dirichlet energy of
the log-cutoff is at most `2π·C²/(−log ε)`, which tends to `0` as `ε → 0`. -/
theorem energy_logCutoff_le (hε : 0 < ε) (hε1 : ε < 1) {C : ℝ}
    (hC : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C) :
    ∫ z : ℂ, ‖fderiv ℝ (logCutoff ε z₀) z‖ ^ 2
      ≤ 2 * Real.pi * C ^ 2 / (-Real.log ε) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hlog : Real.log ε < 0 := Real.log_neg hε hε1
  have hc : (0 : ℝ) < -Real.log ε := by linarith
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  -- the majorant: (C/(−log ε))² · (the radial indicator of r⁻²), centered at z₀
  set K : ℝ := (C / (-Real.log ε)) ^ 2 with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hmaj : ∀ z : ℂ, ‖fderiv ℝ (logCutoff ε z₀) z‖ ^ 2
      ≤ K * indicator (Icc (ε ^ 2) ε) (fun t : ℝ => (t ^ 2)⁻¹) ‖z - z₀‖ := by
    intro z
    rcases lt_or_ge ‖z - z₀‖ (ε ^ 2) with h | h
    · rw [fderiv_logCutoff_inner z₀ hε hε1 h]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      exact mul_nonneg hK0 (indicator_nonneg (fun t _ => by positivity) _)
    rcases le_or_gt ‖z - z₀‖ ε with h2 | h2
    · have hz : z ≠ z₀ := by
        intro hzz
        rw [hzz, sub_self, norm_zero] at h
        linarith
      have hb := norm_fderiv_logCutoff_le z₀ hε hε1 hC hz
      have hmem : ‖z - z₀‖ ∈ Icc (ε ^ 2) ε := ⟨h, h2⟩
      rw [indicator_of_mem hmem]
      have hr : (0 : ℝ) < ‖z - z₀‖ := lt_of_lt_of_le hε2 h
      calc ‖fderiv ℝ (logCutoff ε z₀) z‖ ^ 2
          ≤ (C / (‖z - z₀‖ * (-Real.log ε))) ^ 2 := by
            apply pow_le_pow_left₀ (norm_nonneg _) hb
        _ = K * (‖z - z₀‖ ^ 2)⁻¹ := by
            rw [hKdef]
            field_simp
    · rw [fderiv_logCutoff_outer z₀ hε hε1 h2]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      exact mul_nonneg hK0 (indicator_nonneg (fun t _ => by positivity) _)
  -- integrability of the majorant (bounded, support in a finite-measure ball)
  set g : ℂ → ℝ :=
    fun z => indicator (Icc (ε ^ 2) ε) (fun t : ℝ => (t ^ 2)⁻¹) ‖z - z₀‖ with hgdef
  have hgmeas : Measurable g := by
    exact (Measurable.indicator ((measurable_id.pow_const 2).inv)
      measurableSet_Icc).comp (measurable_norm.comp (measurable_id.sub_const z₀))
  have hg0 : ∀ z, 0 ≤ g z :=
    fun z => indicator_nonneg (fun t _ => by positivity) _
  have hgbd : ∀ z : ℂ, g z ≤
      indicator (Metric.closedBall z₀ ε) (fun _ => ((ε ^ 2) ^ 2)⁻¹) z := by
    intro z
    by_cases hmem : ‖z - z₀‖ ∈ Icc (ε ^ 2) ε
    · have hz : z ∈ Metric.closedBall z₀ ε := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hmem.2
      rw [hgdef]
      simp only [indicator_of_mem hmem, indicator_of_mem hz]
      have h1 : (ε ^ 2) ^ 2 ≤ ‖z - z₀‖ ^ 2 := by nlinarith [hmem.1, hε2.le]
      exact inv_anti₀ (by positivity) h1
    · rw [hgdef]
      simp only [indicator_of_notMem hmem]
      exact indicator_nonneg (fun _ _ => by positivity) _
  have hgi : MeasureTheory.Integrable g := by
    apply MeasureTheory.Integrable.mono'
      (g := fun z => indicator (Metric.closedBall z₀ ε) (fun _ => ((ε ^ 2) ^ 2)⁻¹) z)
    · rw [MeasureTheory.integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
      exact MeasureTheory.integrableOn_const (ne_of_lt measure_closedBall_lt_top)
    · exact hgmeas.aestronglyMeasurable
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 z)]
      exact hgbd z
  -- assemble
  calc ∫ z : ℂ, ‖fderiv ℝ (logCutoff ε z₀) z‖ ^ 2
      ≤ ∫ z : ℂ, K * g z := by
        apply MeasureTheory.integral_mono_of_nonneg
        · filter_upwards with z; positivity
        · exact hgi.const_mul K
        · filter_upwards with z; exact hmaj z
    _ = K * ∫ z : ℂ, g z := MeasureTheory.integral_const_mul K g
    _ = K * (2 * Real.pi * (-Real.log ε)) := by
        rw [hgdef]
        have ht : (∫ z : ℂ,
            indicator (Icc (ε ^ 2) ε) (fun t : ℝ => (t ^ 2)⁻¹) ‖z - z₀‖)
            = ∫ w : ℂ, indicator (Icc (ε ^ 2) ε) (fun t : ℝ => (t ^ 2)⁻¹) ‖w‖ :=
          MeasureTheory.integral_sub_right_eq_self
            (fun w : ℂ => indicator (Icc (ε ^ 2) ε) (fun t : ℝ => (t ^ 2)⁻¹) ‖w‖) z₀
        rw [ht, integral_indicator_inv_sq_norm hε hε1]
    _ = 2 * Real.pi * C ^ 2 / (-Real.log ε) := by
        rw [hKdef]
        field_simp

end KsIndex.LogCutoff
