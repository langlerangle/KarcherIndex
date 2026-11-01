module

/-
KsIndexLean — A two-dimensional logarithmic cutoff at a point.

For `0 < ε < 1`, the cutoff at `p` is zero on `‖w-p‖ ≤ ε²`, one on
`‖w-p‖ ≥ ε`, smooth on the plane, and valued in `[0,1]`. Away from `p`,
it is `ψ((log ‖w-p‖ - 2*log ε) / log(1/ε))`, where
`ψ = Real.smoothTransition`; its value at `p` is defined to be zero.

The constant `Mψ` is a chosen nonnegative uniform bound for `|ψ'|`.
Writing `L = log(1/ε)`, the derivative norm is at most
`Mψ/(L*‖w-p‖)` away from `p`. The gradient density vanishes outside the
closed annulus and is bounded there by `2*Mψ²/(L²*‖w-p‖²)`.

The file evaluates the radial annular majorant and proves the disk-energy
bound `∫_disk gradSq (cut1C ε p) ≤ 4*π*Mψ² / log(1/ε)`. These estimates
supply cutoffs for imposing vanishing near punctures in the test spaces.
-/
public import Mathlib
public import KsIndexLean.Surface

@[expose] public section


noncomputable section

open Real Filter Topology MeasureTheory
open scoped ContDiff

namespace KsIndex.PunctureCutoff

/-! ### The derivative of the smooth transition is bounded -/

lemma smoothTransition_deriv_eq_zero_of_neg {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
  rw [h.deriv_eq, deriv_const]

lemma smoothTransition_deriv_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
  rw [h.deriv_eq, deriv_const]

/-- A uniform bound on `|ψ'|`. -/
lemma smoothTransition_deriv_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |deriv Real.smoothTransition x| ≤ M := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  rcases lt_or_ge x 0 with h | h
  · rw [smoothTransition_deriv_eq_zero_of_neg h, abs_zero]; exact le_max_right _ _
  rcases le_or_gt x 1 with h1 | h1
  · exact le_trans (by simpa [Real.norm_eq_abs] using hM x ⟨h, h1⟩) (le_max_left _ _)
  · rw [smoothTransition_deriv_eq_zero_of_one_lt h1, abs_zero]; exact le_max_right _ _

/-- A chosen nonnegative uniform upper bound for `|ψ'|`. -/
def Mψ : ℝ := Classical.choose smoothTransition_deriv_bound

lemma Mψ_nonneg : 0 ≤ Mψ := (Classical.choose_spec smoothTransition_deriv_bound).1

lemma abs_deriv_smoothTransition_le (x : ℝ) : |deriv Real.smoothTransition x| ≤ Mψ :=
  (Classical.choose_spec smoothTransition_deriv_bound).2 x

/-! ### The cutoff -/

/-- `L = log(1/ε)`. -/
def Lε (ε : ℝ) : ℝ := -Real.log ε

lemma Lε_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) : 0 < Lε ε := by
  unfold Lε; linarith [Real.log_neg h0 h1]

/-- The argument of the transition: `(log|w−p| − 2 log ε)/L`, written with `log(|w−p|²)/2`. -/
def arg (ε : ℝ) (p w : ℂ) : ℝ := (Lε ε)⁻¹ * (2⁻¹ * Real.log (‖w - p‖ ^ 2) - 2 * Real.log ε)

/-- The logarithmic cutoff at `p`. For `0 < ε < 1`, it is `0` on
`|w−p| ≤ ε²` and `1` on `|w−p| ≥ ε`. -/
def cut1 (ε : ℝ) (p w : ℂ) : ℝ := if w = p then 0 else Real.smoothTransition (arg ε p w)

lemma cut1_nonneg (ε : ℝ) (p w : ℂ) : 0 ≤ cut1 ε p w := by
  unfold cut1; split_ifs
  · exact le_rfl
  · exact Real.smoothTransition.nonneg _

lemma cut1_le_one (ε : ℝ) (p w : ℂ) : cut1 ε p w ≤ 1 := by
  unfold cut1; split_ifs
  · exact zero_le_one
  · exact Real.smoothTransition.le_one _

lemma log_norm_sq_half (w p : ℂ) :
    2⁻¹ * Real.log (‖w - p‖ ^ 2) = Real.log ‖w - p‖ := by
  rw [Real.log_pow]; push_cast; ring

/-- `cut1 = 0` on the small disk `|w − p| ≤ ε²`. -/
lemma cut1_eq_zero {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {p w : ℂ} (hw : ‖w - p‖ ≤ ε ^ 2) :
    cut1 ε p w = 0 := by
  unfold cut1
  split_ifs with h
  · rfl
  · apply Real.smoothTransition.zero_of_nonpos
    have hL := Lε_pos h0 h1
    have hpos : 0 < ‖w - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
    have hlog : Real.log ‖w - p‖ ≤ 2 * Real.log ε := by
      have := Real.log_le_log hpos hw
      rw [Real.log_pow] at this; push_cast at this; linarith
    unfold arg
    rw [log_norm_sq_half]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hL).le (by linarith)

/-- `cut1 = 1` off the disk `|w − p| < ε`. -/
lemma cut1_eq_one {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {p w : ℂ} (hw : ε ≤ ‖w - p‖) :
    cut1 ε p w = 1 := by
  have hne : w ≠ p := by
    intro h; subst h; simp at hw; linarith
  unfold cut1
  rw [if_neg hne]
  apply Real.smoothTransition.one_of_one_le
  have hL := Lε_pos h0 h1
  have hlog : Real.log ε ≤ Real.log ‖w - p‖ := Real.log_le_log h0 hw
  unfold arg
  rw [log_norm_sq_half, ← div_eq_inv_mul, le_div_iff₀ hL]
  unfold Lε; linarith

/-! ### Smoothness -/

lemma contDiffAt_arg {ε : ℝ} {p w : ℂ} (hw : w ≠ p) : ContDiffAt ℝ ∞ (arg ε p) w := by
  have h1 : ContDiffAt ℝ ∞ (fun z : ℂ => ‖z - p‖ ^ 2) w := by
    have : ContDiffAt ℝ ∞ (fun z : ℂ => z - p) w := contDiffAt_id.sub contDiffAt_const
    exact (this.norm ℝ (sub_ne_zero.mpr hw)).pow 2
  have h2 : ContDiffAt ℝ ∞ (fun z : ℂ => Real.log (‖z - p‖ ^ 2)) w :=
    h1.log (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hw)) 2).ne'
  exact contDiffAt_const.mul ((contDiffAt_const.mul h2).sub contDiffAt_const)

/-- The cutoff is `C^∞` on all of `ℂ`. -/
lemma cut1_contDiff {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (p : ℂ) : ContDiff ℝ ∞ (cut1 ε p) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : ‖w - p‖ < ε ^ 2
  · -- locally zero
    have hloc : cut1 ε p =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
      have hopen : IsOpen {z : ℂ | ‖z - p‖ < ε ^ 2} :=
        isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
      filter_upwards [hopen.mem_nhds hw] with z hz
      exact cut1_eq_zero h0 h1 (le_of_lt hz)
    exact contDiffAt_const.congr_of_eventuallyEq hloc
  · have hne : w ≠ p := by
      intro h; subst h; apply hw; simp only [sub_self, norm_zero]; positivity
    have hloc : cut1 ε p =ᶠ[𝓝 w] fun z => Real.smoothTransition (arg ε p z) := by
      filter_upwards [isOpen_ne.mem_nhds hne] with z hz
      exact if_neg hz
    refine ContDiffAt.congr_of_eventuallyEq ?_ hloc
    exact (Real.smoothTransition.contDiff (n := ⊤)).contDiffAt.comp w (contDiffAt_arg hne)

/-! ### The gradient bound -/

/-- Derivative of `arg` at `w ≠ p`: `(1/L)·⟪w−p, ·⟫/‖w−p‖²`. -/
lemma hasFDerivAt_arg {ε : ℝ} {p w : ℂ} (hw : w ≠ p) :
    HasFDerivAt (arg ε p)
      ((Lε ε)⁻¹ • ((‖w - p‖ ^ 2)⁻¹ • innerSL ℝ (w - p))) w := by
  have hsub : HasFDerivAt (fun z : ℂ => z - p) (ContinuousLinearMap.id ℝ ℂ) w :=
    (hasFDerivAt_id w).sub_const p
  have hsq : HasFDerivAt (fun z : ℂ => ‖z - p‖ ^ 2) (2 • innerSL ℝ (w - p)) w := by
    have := (hasStrictFDerivAt_norm_sq (w - p)).hasFDerivAt.comp w hsub
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  have hne : ‖w - p‖ ^ 2 ≠ 0 := by
    have : 0 < ‖w - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw)
    positivity
  have hlog : HasFDerivAt (fun z : ℂ => Real.log (‖z - p‖ ^ 2))
      ((‖w - p‖ ^ 2)⁻¹ • (2 • innerSL ℝ (w - p))) w := hsq.log hne
  have h := ((hlog.const_mul (2⁻¹ : ℝ)).sub_const (2 * Real.log ε)).const_mul (Lε ε)⁻¹
  refine h.congr_fderiv ?_
  ext v
  simp only [map_sub, smul_apply, sub_apply,
    coe_innerSL_apply, Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg,
    sub_neg_eq_add, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul, mul_eq_mul_left_iff, inv_eq_zero]
  left; ring

lemma norm_fderiv_arg_le {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {p w : ℂ} (hw : w ≠ p) :
    ‖fderiv ℝ (arg ε p) w‖ ≤ (Lε ε)⁻¹ * ‖w - p‖⁻¹ := by
  rw [(hasFDerivAt_arg (ε := ε) hw).fderiv, norm_smul, norm_smul, innerSL_apply_norm]
  have hL := Lε_pos h0 h1
  have hpos : 0 < ‖w - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw)
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by positivity))]
  apply le_of_eq
  field_simp

/-- The cutoff's Fréchet derivative at `w ≠ p`: `ψ'(arg)·d(arg)`. -/
lemma hasFDerivAt_cut1 {ε : ℝ} {p w : ℂ} (hw : w ≠ p) :
    HasFDerivAt (cut1 ε p)
      (deriv Real.smoothTransition (arg ε p w) • fderiv ℝ (arg ε p) w) w := by
  have hψ : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (arg ε p w))
      (arg ε p w) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) _).hasDerivAt
  have hg : HasFDerivAt (arg ε p) (fderiv ℝ (arg ε p) w) w :=
    (hasFDerivAt_arg (ε := ε) hw).differentiableAt.hasFDerivAt
  have hc := hψ.comp_hasFDerivAt w hg
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hw] with z hz
  exact if_neg hz

/-- **Pointwise gradient bound**: `‖∇ cut1‖ ≤ M/(L·|w−p|)` at `w ≠ p`. -/
lemma norm_fderiv_cut1_le {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {p w : ℂ} (hw : w ≠ p) :
    ‖fderiv ℝ (cut1 ε p) w‖ ≤ Mψ * ((Lε ε)⁻¹ * ‖w - p‖⁻¹) := by
  rw [(hasFDerivAt_cut1 (ε := ε) hw).fderiv, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (abs_deriv_smoothTransition_le _) (norm_fderiv_arg_le h0 h1 hw)
    (norm_nonneg _) Mψ_nonneg

/-- The flat gradient density (as in `Surface.gradSq`, real-valued version) is bounded by
`2‖df‖²`. -/
lemma gradSqR_le {f : ℂ → ℝ} (w : ℂ) :
    ‖fderiv ℝ f w 1‖ ^ 2 + ‖fderiv ℝ f w Complex.I‖ ^ 2 ≤ 2 * ‖fderiv ℝ f w‖ ^ 2 := by
  have h1 : ‖fderiv ℝ f w 1‖ ≤ ‖fderiv ℝ f w‖ := by
    simpa using (fderiv ℝ f w).le_opNorm 1
  have h2 : ‖fderiv ℝ f w Complex.I‖ ≤ ‖fderiv ℝ f w‖ := by
    simpa using (fderiv ℝ f w).le_opNorm Complex.I
  nlinarith [norm_nonneg (fderiv ℝ f w 1), norm_nonneg (fderiv ℝ f w Complex.I),
    norm_nonneg (fderiv ℝ f w)]

/-- **The gradient density of the cutoff**: `≤ 2M²/(L²|w−p|²)` on the closed annulus
`ε² ≤ |w−p| ≤ ε`, and `= 0` off it (the cutoff is locally constant there). -/
lemma gradSq_cut1_le {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (p w : ℂ) :
    ‖fderiv ℝ (cut1 ε p) w 1‖ ^ 2 + ‖fderiv ℝ (cut1 ε p) w Complex.I‖ ^ 2
      ≤ if ε ^ 2 ≤ ‖w - p‖ ∧ ‖w - p‖ ≤ ε
          then 2 * Mψ ^ 2 * ((Lε ε)⁻¹ * ‖w - p‖⁻¹) ^ 2 else 0 := by
  split_ifs with h
  · have hne : w ≠ p := by
      intro hh; subst hh; simp at h; nlinarith [h.1]
    calc _ ≤ 2 * ‖fderiv ℝ (cut1 ε p) w‖ ^ 2 := gradSqR_le w
      _ ≤ 2 * (Mψ * ((Lε ε)⁻¹ * ‖w - p‖⁻¹)) ^ 2 := by
          gcongr
          exact norm_fderiv_cut1_le h0 h1 hne
      _ = _ := by ring
  · have hzero : fderiv ℝ (cut1 ε p) w = 0 := by
      push Not at h
      rcases lt_or_ge ‖w - p‖ (ε ^ 2) with hlt | hge
      · have hloc : cut1 ε p =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
          have hopen : IsOpen {z : ℂ | ‖z - p‖ < ε ^ 2} :=
            isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
          filter_upwards [hopen.mem_nhds hlt] with z hz
          exact cut1_eq_zero h0 h1 (le_of_lt hz)
        rw [hloc.fderiv_eq]; simp
      · have hgt : ε < ‖w - p‖ := h hge
        have hloc : cut1 ε p =ᶠ[𝓝 w] fun _ => (1 : ℝ) := by
          have hopen : IsOpen {z : ℂ | ε < ‖z - p‖} :=
            isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
          filter_upwards [hopen.mem_nhds hgt] with z hz
          exact cut1_eq_one h0 h1 (le_of_lt hz)
        rw [hloc.fderiv_eq]; simp
    rw [hzero]; simp

/-! ### The radial annulus integral -/

/-- The radial cutoff-energy density on the plane. -/
def annDens (ε : ℝ) (x : ℂ) : ℝ :=
  if ε ^ 2 ≤ ‖x‖ ∧ ‖x‖ ≤ ε then (‖x‖⁻¹) ^ 2 else 0

/-- The radial profile of `annDens`: `annDens ε x = annProf ε ‖x‖`. -/
private def annProf (ε : ℝ) (r : ℝ) : ℝ :=
  if ε ^ 2 ≤ r ∧ r ≤ ε then (r⁻¹) ^ 2 else 0

private lemma annDens_eq (ε : ℝ) : annDens ε = fun x : ℂ => annProf ε ‖x‖ := rfl

/-- The weighted radial profile appearing in `integral_fun_norm_addHaar` is the
indicator of `[ε², ε]` of `y ↦ y⁻¹`. -/
private lemma smul_annProf_eq_indicator {ε : ℝ} (h0 : 0 < ε) :
    (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • annProf ε y)
      = Set.indicator (Set.Icc (ε ^ 2) ε) (fun y : ℝ => y⁻¹) := by
  funext y
  rw [Complex.finrank_real_complex]
  by_cases hy : ε ^ 2 ≤ y ∧ y ≤ ε
  · have hpos : 0 < y := lt_of_lt_of_le (by positivity) hy.1
    rw [Set.indicator_of_mem (Set.mem_Icc.2 hy)]
    simp only [annProf, if_pos hy, smul_eq_mul]
    field_simp
    ring
  · rw [Set.indicator_of_notMem (by simpa [Set.mem_Icc] using hy)]
    simp [annProf, hy]

private lemma integrableOn_inv_Icc {ε : ℝ} (h0 : 0 < ε) :
    IntegrableOn (fun y : ℝ => y⁻¹) (Set.Icc (ε ^ 2) ε) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  intro y hy
  have : y ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity) hy.1)
  exact (continuousAt_inv₀ this).continuousWithinAt

theorem annDens_integrable {ε : ℝ} (h0 : 0 < ε) (_h1 : ε < 1) :
    Integrable (annDens ε) (volume : Measure ℂ) := by
  rw [annDens_eq, integrable_fun_norm_addHaar, smul_annProf_eq_indicator h0]
  exact ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_inv_Icc h0)).integrableOn

theorem annDens_integral {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ∫ x : ℂ, annDens ε x = 2 * π * (-Real.log ε) := by
  have hsub : Set.Icc (ε ^ 2) ε ⊆ Set.Ioi (0 : ℝ) := fun y hy =>
    lt_of_lt_of_le (by positivity) hy.1
  have hle : ε ^ 2 ≤ ε := by nlinarith
  have key : ∫ y in Set.Ioi (0:ℝ), y ^ (Module.finrank ℝ ℂ - 1) • annProf ε y
      = -Real.log ε := by
    rw [smul_annProf_eq_indicator h0, setIntegral_indicator measurableSet_Icc,
      Set.inter_eq_right.2 hsub, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle, integral_inv_of_pos (by positivity) h0]
    rw [Real.log_div h0.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  rw [annDens_eq, integral_fun_norm_addHaar, key, Complex.finrank_real_complex]
  have hball : (volume (Metric.ball (0:ℂ) 1)).toReal = π := by simp [Complex.volume_ball]
  simp only [Measure.real, hball, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-! ### The energy of the cutoff -/

/-- The complex-valued cutoff (for `Surface.gradSq`). -/
def cut1C (ε : ℝ) (p w : ℂ) : ℂ := (cut1 ε p w : ℂ)

lemma gradSq_cut1C {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (p w : ℂ) :
    KsIndex.Surface.gradSq (cut1C ε p) w
      = ‖fderiv ℝ (cut1 ε p) w 1‖ ^ 2 + ‖fderiv ℝ (cut1 ε p) w Complex.I‖ ^ 2 := by
  have hd : DifferentiableAt ℝ (cut1 ε p) w :=
    ((cut1_contDiff h0 h1 p).differentiable (by simp)) w
  have hc : cut1C ε p = ⇑Complex.ofRealCLM ∘ cut1 ε p := rfl
  unfold KsIndex.Surface.gradSq
  rw [hc, (Complex.ofRealCLM.hasFDerivAt.comp w hd.hasFDerivAt).fderiv]
  simp [Complex.norm_real]

/-- The dominating density `2Mψ²/L² · annDens ε (w − p)`. -/
lemma gradSq_cut1C_le {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (p w : ℂ) :
    KsIndex.Surface.gradSq (cut1C ε p) w ≤ 2 * Mψ ^ 2 * (Lε ε)⁻¹ ^ 2 * annDens ε (w - p) := by
  rw [gradSq_cut1C h0 h1]
  refine le_trans (gradSq_cut1_le h0 h1 p w) ?_
  unfold annDens
  split_ifs with h
  · apply le_of_eq; ring
  · simp

lemma measurable_gradSq (f : ℂ → ℂ) : Measurable (KsIndex.Surface.gradSq f) := by
  unfold KsIndex.Surface.gradSq
  exact ((measurable_fderiv_apply_const ℝ f 1).norm.pow_const 2).add
    ((measurable_fderiv_apply_const ℝ f Complex.I).norm.pow_const 2)

/-- **The Dirichlet energy of the cutoff on the disk is `O(1/L)`**:
`∫_D |∇ cut1|² ≤ 4π Mψ² / log(1/ε)`. -/
theorem energy_cut1_le {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (p : ℂ) :
    ∫ w in KsIndex.Surface.disk, KsIndex.Surface.gradSq (cut1C ε p) w
      ≤ 4 * π * Mψ ^ 2 / Lε ε := by
  have hL := Lε_pos h0 h1
  set B : ℂ → ℝ := fun w => 2 * Mψ ^ 2 * (Lε ε)⁻¹ ^ 2 * annDens ε (w - p) with hB
  have hBint : Integrable B := ((annDens_integrable h0 h1).comp_sub_right p).const_mul _
  have hBval : ∫ w, B w = 2 * Mψ ^ 2 * (Lε ε)⁻¹ ^ 2 * (2 * π * Lε ε) := by
    simp only [hB]
    rw [integral_const_mul, integral_sub_right_eq_self (annDens ε) p, annDens_integral h0 h1]
    rfl
  have hle : ∀ w, KsIndex.Surface.gradSq (cut1C ε p) w ≤ B w := fun w =>
    gradSq_cut1C_le h0 h1 p w
  have hnn : ∀ w, 0 ≤ KsIndex.Surface.gradSq (cut1C ε p) w := fun w => by
    unfold KsIndex.Surface.gradSq; positivity
  have hint : Integrable (KsIndex.Surface.gradSq (cut1C ε p)) :=
    hBint.mono' (measurable_gradSq _).aestronglyMeasurable
      (Eventually.of_forall fun w => by rw [Real.norm_eq_abs, abs_of_nonneg (hnn w)]; exact hle w)
  calc ∫ w in KsIndex.Surface.disk, KsIndex.Surface.gradSq (cut1C ε p) w
      ≤ ∫ w, KsIndex.Surface.gradSq (cut1C ε p) w :=
        setIntegral_le_integral hint (Eventually.of_forall hnn)
    _ ≤ ∫ w, B w := integral_mono hint hBint hle
    _ = 2 * Mψ ^ 2 * (Lε ε)⁻¹ ^ 2 * (2 * π * Lε ε) := hBval
    _ = 4 * π * Mψ ^ 2 / Lε ε := by field_simp; ring

end KsIndex.PunctureCutoff
