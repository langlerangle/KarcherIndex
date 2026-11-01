module

/-
# Laplacian of a logarithmic cutoff

For `w ≠ p`, the real cutoff satisfies
`Δ (cut1 ε p) w = ψ''(arg ε p w) / (L‖w−p‖)²`, where `L = Lε ε`.
The directional chain rule gives a second-derivative term and a first-derivative
term. The latter vanishes because the divergence of `(x,y)/r²` is zero away
from the origin; the squared directional derivatives of `arg` sum to `1/(Lr)²`.

For `0 < ε < 1`, this identity transfers to the complex-valued cutoff `cut1C`.
Its Laplacian vanishes outside the closed annulus `ε² ≤ ‖w−p‖ ≤ ε` and is
bounded there by `Mψ₂/(Lr)²`, where `Mψ₂` is a chosen nonnegative uniform bound
on `|ψ''|`. Radial integration gives
`∫ ‖Δ (cut1C ε p)‖ ≤ 2π·Mψ₂/L`.
This quantitative estimate controls the cutoff-Laplacian term in puncture
removal arguments. The file proves the estimate; limit arguments using it
are supplied by consumers.
-/
public import KsIndexLean.PunctureCutoff
public import KsIndexLean.GreenIdentity

@[expose] public section


noncomputable section

open Real Filter Topology MeasureTheory
open scoped ContDiff

namespace KsIndex.CutLaplacian

open KsIndex.PunctureCutoff KsIndex.Surface KsIndex.Green

/-! ### A uniform bound on `ψ''` -/

lemma smoothTransition_deriv2_eq_zero_of_neg {x : ℝ} (hx : x < 0) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have h : deriv Real.smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact smoothTransition_deriv_eq_zero_of_neg (Set.mem_Iio.mp hy)
  rw [h.deriv_eq, deriv_const]

lemma smoothTransition_deriv2_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have h : deriv Real.smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact smoothTransition_deriv_eq_zero_of_one_lt (Set.mem_Ioi.mp hy)
  rw [h.deriv_eq, deriv_const]

/-- A uniform bound on `|ψ''|` (zero outside `[0,1]`, bounded on it by compactness). -/
lemma smoothTransition_deriv2_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ M := by
  have hd1 : ContDiff ℝ 1 (deriv Real.smoothTransition) :=
    (contDiff_succ_iff_deriv.mp (Real.smoothTransition.contDiff (n := 2))).2.2
  have hc : Continuous (deriv (deriv Real.smoothTransition)) := hd1.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  rcases lt_or_ge x 0 with h | h
  · rw [smoothTransition_deriv2_eq_zero_of_neg h, abs_zero]; exact le_max_right _ _
  rcases le_or_gt x 1 with h1 | h1
  · exact le_trans (by simpa [Real.norm_eq_abs] using hM x ⟨h, h1⟩) (le_max_left _ _)
  · rw [smoothTransition_deriv2_eq_zero_of_one_lt h1, abs_zero]; exact le_max_right _ _

/-- A chosen nonnegative uniform bound on `|ψ''|`; not necessarily the least bound. -/
def Mψ₂ : ℝ := Classical.choose smoothTransition_deriv2_bound

lemma Mψ₂_nonneg : 0 ≤ Mψ₂ := (Classical.choose_spec smoothTransition_deriv2_bound).1

lemma abs_deriv2_smoothTransition_le (x : ℝ) :
    |deriv (deriv Real.smoothTransition) x| ≤ Mψ₂ :=
  (Classical.choose_spec smoothTransition_deriv2_bound).2 x

/-! ### The directional derivative of `arg` in coordinates -/

/-- `av ε p v z = ⟨z−p, v⟩/(L‖z−p‖²)`: the closed form of `∂_v (arg ε p)` at `z ≠ p`. -/
def av (ε : ℝ) (p v z : ℂ) : ℝ :=
  (Lε ε)⁻¹ * (((z - p).re * v.re + (z - p).im * v.im) * (‖z - p‖ ^ 2)⁻¹)

lemma fderiv_arg_apply {ε : ℝ} {p w : ℂ} (hw : w ≠ p) (v : ℂ) :
    fderiv ℝ (arg ε p) w v = av ε p v w := by
  rw [(hasFDerivAt_arg (ε := ε) hw).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, av, coe_innerSL_apply,
    Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]
  ring

/-! ### `HasFDerivAt` for the building blocks at `w ≠ p` -/

/-- The derivative of the squared distance `‖z−p‖²`. -/
lemma hasFDerivAt_normSq_sub (p w : ℂ) :
    HasFDerivAt (fun z : ℂ => ‖z - p‖ ^ 2) (2 • innerSL ℝ (w - p)) w := by
  have hsub : HasFDerivAt (fun z : ℂ => z - p) (ContinuousLinearMap.id ℝ ℂ) w :=
    (hasFDerivAt_id w).sub_const p
  have := (hasStrictFDerivAt_norm_sq (w - p)).hasFDerivAt.comp w hsub
  rwa [ContinuousLinearMap.comp_id] at this

/-- The linear numerator `⟨z−p, v⟩`. -/
lemma hasFDerivAt_nv (p v w : ℂ) :
    HasFDerivAt (fun z : ℂ => (z - p).re * v.re + (z - p).im * v.im)
      (v.re • (Complex.reCLM : ℂ →L[ℝ] ℝ) + v.im • (Complex.imCLM : ℂ →L[ℝ] ℝ)) w := by
  have hre : HasFDerivAt (fun z : ℂ => (z - p).re) (Complex.reCLM : ℂ →L[ℝ] ℝ) w := by
    have h := (Complex.reCLM.hasFDerivAt (x := w)).sub_const p.re
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    simp [Complex.sub_re]
  have him : HasFDerivAt (fun z : ℂ => (z - p).im) (Complex.imCLM : ℂ →L[ℝ] ℝ) w := by
    have h := (Complex.imCLM.hasFDerivAt (x := w)).sub_const p.im
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    simp [Complex.sub_im]
  have h1 : HasFDerivAt (fun z : ℂ => (z - p).re * v.re)
      (v.re • (Complex.reCLM : ℂ →L[ℝ] ℝ)) w := by
    simpa [smul_smul, mul_comm] using hre.mul_const v.re
  have h2 : HasFDerivAt (fun z : ℂ => (z - p).im * v.im)
      (v.im • (Complex.imCLM : ℂ →L[ℝ] ℝ)) w := by
    simpa [smul_smul, mul_comm] using him.mul_const v.im
  exact h1.add h2

lemma norm_sub_sq_ne_zero {p w : ℂ} (hw : w ≠ p) : ‖w - p‖ ^ 2 ≠ 0 := by
  have : 0 < ‖w - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw)
  positivity

/-- The inverse of the norm-square. -/
lemma hasFDerivAt_normSq_inv (p : ℂ) {w : ℂ} (hw : w ≠ p) :
    HasFDerivAt (fun z : ℂ => (‖z - p‖ ^ 2)⁻¹)
      ((-((‖w - p‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ (w - p))) w := by
  have hd : HasDerivAt (fun t : ℝ => t⁻¹) (-((‖w - p‖ ^ 2) ^ 2)⁻¹) (‖w - p‖ ^ 2) :=
    hasDerivAt_inv (norm_sub_sq_ne_zero hw)
  exact hd.comp_hasFDerivAt w (hasFDerivAt_normSq_sub p w)

/-- `av` as the `HasFDerivAt` chain `L⁻¹·(N·D⁻¹)`; the derivative is whatever the chain gives. -/
lemma hasFDerivAt_av {ε : ℝ} (p v : ℂ) {w : ℂ} (hw : w ≠ p) :
    HasFDerivAt (av ε p v)
      ((Lε ε)⁻¹ • ((((w - p).re * v.re + (w - p).im * v.im)
          • ((-((‖w - p‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ (w - p))))
        + (‖w - p‖ ^ 2)⁻¹
          • (v.re • (Complex.reCLM : ℂ →L[ℝ] ℝ) + v.im • (Complex.imCLM : ℂ →L[ℝ] ℝ)))) w := by
  have hmul := (hasFDerivAt_nv p v w).mul (hasFDerivAt_normSq_inv p hw)
  exact hmul.const_mul ((Lε ε)⁻¹)

lemma differentiableAt_av {ε : ℝ} (p v : ℂ) {w : ℂ} (hw : w ≠ p) :
    DifferentiableAt ℝ (av ε p v) w := (hasFDerivAt_av p v hw).differentiableAt

/-- The directional value of `∂av` at the same direction `v`: the quotient-rule numerator. -/
lemma fderiv_av_apply {ε : ℝ} (p v : ℂ) {w : ℂ} (hw : w ≠ p) :
    fderiv ℝ (av ε p v) w v
      = (Lε ε)⁻¹ * (((v.re ^ 2 + v.im ^ 2) * ‖w - p‖ ^ 2
          - 2 * ((w - p).re * v.re + (w - p).im * v.im) ^ 2) * ((‖w - p‖ ^ 2) ^ 2)⁻¹) := by
  have hne := norm_sub_sq_ne_zero hw
  rw [(hasFDerivAt_av p v hw).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    smul_eq_mul, coe_innerSL_apply, Complex.inner, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, mul_neg, sub_neg_eq_add, nsmul_eq_mul, Nat.cast_ofNat, neg_mul]
  field_simp
  ring

/-! ### The second directional derivative of `cut1` -/

lemma differentiable_deriv_smoothTransition :
    Differentiable ℝ (deriv Real.smoothTransition) := by
  have hd1 : ContDiff ℝ 1 (deriv Real.smoothTransition) :=
    (contDiff_succ_iff_deriv.mp (Real.smoothTransition.contDiff (n := 2))).2.2
  exact hd1.differentiable one_ne_zero

/-- `∂_v ∂_v cut1 = ψ''(arg)·(av v)² + ψ'(arg)·∂_v(av v)` at `w ≠ p`. -/
lemma fderiv_fderiv_cut1_apply {ε : ℝ} {p w : ℂ} (hw : w ≠ p) (v : ℂ) :
    fderiv ℝ (fun z => fderiv ℝ (cut1 ε p) z v) w v
      = deriv (deriv Real.smoothTransition) (arg ε p w) * av ε p v w ^ 2
        + deriv Real.smoothTransition (arg ε p w) * fderiv ℝ (av ε p v) w v := by
  -- the inner function agrees with the explicit product near w
  have hev : (fun z => fderiv ℝ (cut1 ε p) z v)
      =ᶠ[nhds w] fun z => deriv Real.smoothTransition (arg ε p z) * av ε p v z := by
    filter_upwards [isOpen_ne.mem_nhds hw] with z hz
    rw [(hasFDerivAt_cut1 (ε := ε) hz).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_arg_apply hz]
  rw [hev.fderiv_eq]
  -- product rule for ψ'(arg)·av
  have harg : HasFDerivAt (arg ε p) (fderiv ℝ (arg ε p) w) w :=
    (hasFDerivAt_arg (ε := ε) hw).differentiableAt.hasFDerivAt
  have hψ' : HasFDerivAt (fun z => deriv Real.smoothTransition (arg ε p z))
      (deriv (deriv Real.smoothTransition) (arg ε p w) • fderiv ℝ (arg ε p) w) w := by
    have hd : HasDerivAt (deriv Real.smoothTransition)
        (deriv (deriv Real.smoothTransition) (arg ε p w)) (arg ε p w) :=
      (differentiable_deriv_smoothTransition _).hasDerivAt
    exact hd.comp_hasFDerivAt w harg
  have hav : HasFDerivAt (av ε p v) (fderiv ℝ (av ε p v) w) w :=
    (differentiableAt_av p v hw).hasFDerivAt
  have hmul := hψ'.mul hav
  have hfd : fderiv ℝ (fun z => deriv Real.smoothTransition (arg ε p z) * av ε p v z) w
      = deriv Real.smoothTransition (arg ε p w) • fderiv ℝ (av ε p v) w
        + av ε p v w • (deriv (deriv Real.smoothTransition) (arg ε p w)
          • fderiv ℝ (arg ε p) w) := hmul.fderiv
  rw [hfd]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_arg_apply hw]
  ring

/-! ### The exact Laplacian identity -/

lemma norm_sub_sq_expand (p w : ℂ) : ‖w - p‖ ^ 2 = (w - p).re ^ 2 + (w - p).im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- `A₁² + A_I² = 1/(Lr)²`. -/
lemma sum_av_sq {ε : ℝ} {p w : ℂ} (hw : w ≠ p) :
    av ε p 1 w ^ 2 + av ε p Complex.I w ^ 2 = ((Lε ε)⁻¹ * ‖w - p‖⁻¹) ^ 2 := by
  have hne := norm_sub_sq_ne_zero hw
  have hr := norm_sub_sq_expand p w
  calc av ε p 1 w ^ 2 + av ε p Complex.I w ^ 2
      = (Lε ε)⁻¹ ^ 2 * (((‖w - p‖ ^ 2)⁻¹) ^ 2 * ((w - p).re ^ 2 + (w - p).im ^ 2)) := by
        simp only [av, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
          mul_one, mul_zero, add_zero, zero_add]
        ring
    _ = (Lε ε)⁻¹ ^ 2 * (((‖w - p‖ ^ 2)⁻¹) ^ 2 * ‖w - p‖ ^ 2) := by rw [← hr]
    _ = ((Lε ε)⁻¹ * ‖w - p‖⁻¹) ^ 2 := by
        rw [mul_pow, ← inv_pow]
        congr 1
        field_simp

/-- The `ψ'`-coefficient vanishes: `∂₁A₁ + ∂_I A_I = 0` (the divergence of `(x,y)/r²`). -/
lemma sum_fderiv_av_zero {ε : ℝ} {p w : ℂ} (hw : w ≠ p) :
    fderiv ℝ (av ε p 1) w 1 + fderiv ℝ (av ε p Complex.I) w Complex.I = 0 := by
  have hr := norm_sub_sq_expand p w
  calc fderiv ℝ (av ε p 1) w 1 + fderiv ℝ (av ε p Complex.I) w Complex.I
      = (Lε ε)⁻¹ * ((2 * ‖w - p‖ ^ 2 - 2 * ((w - p).re ^ 2 + (w - p).im ^ 2))
          * (((‖w - p‖ ^ 2) ^ 2)⁻¹)) := by
        rw [fderiv_av_apply p 1 hw, fderiv_av_apply p Complex.I hw]
        simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
        ring
    _ = 0 := by rw [← hr]; ring

/-- **The exact real Laplacian of the cutoff** at `w ≠ p`:
`∂₁²cut1 + ∂_I²cut1 = ψ''(arg)/(L‖w−p‖)²`. -/
lemma lapR_cut1 {ε : ℝ} {p w : ℂ} (hw : w ≠ p) :
    fderiv ℝ (fun z => fderiv ℝ (cut1 ε p) z 1) w 1
      + fderiv ℝ (fun z => fderiv ℝ (cut1 ε p) z Complex.I) w Complex.I
      = deriv (deriv Real.smoothTransition) (arg ε p w) * ((Lε ε)⁻¹ * ‖w - p‖⁻¹) ^ 2 := by
  rw [fderiv_fderiv_cut1_apply hw 1, fderiv_fderiv_cut1_apply hw Complex.I]
  linear_combination deriv (deriv Real.smoothTransition) (arg ε p w) * sum_av_sq (ε := ε) hw
    + deriv Real.smoothTransition (arg ε p w) * sum_fderiv_av_zero (ε := ε) hw

/-! ### Transport to the complex-valued `cut1C` -/

lemma cut1C_contDiff {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (p : ℂ) :
    ContDiff ℝ ∞ (cut1C ε p) := by
  have hc : cut1C ε p = ⇑Complex.ofRealCLM ∘ cut1 ε p := rfl
  rw [hc]
  exact Complex.ofRealCLM.contDiff.comp (cut1_contDiff h0 h1 p)

/-- Directional derivatives commute with the real embedding. -/
lemma fderiv_cut1C_apply {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (p : ℂ) (z v : ℂ) :
    fderiv ℝ (cut1C ε p) z v = ((fderiv ℝ (cut1 ε p) z v : ℝ) : ℂ) := by
  have hc : cut1C ε p = ⇑Complex.ofRealCLM ∘ cut1 ε p := rfl
  have hd : DifferentiableAt ℝ (cut1 ε p) z :=
    (((cut1_contDiff h0 h1 p).contDiffAt).of_le two_le_infty).differentiableAt (by norm_num)
  rw [hc, fderiv_comp z Complex.ofRealCLM.differentiableAt hd, ContinuousLinearMap.fderiv]
  rfl

/-- **The exact Laplacian identity for `cut1C`** at `w ≠ p`:
`Δ(cut1C ε p) w = ψ''(arg w)/(L‖w−p‖)²`. -/
lemma laplacian_cut1C_eq {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {p w : ℂ} (hw : w ≠ p) :
    laplacian (cut1C ε p) w
      = ((deriv (deriv Real.smoothTransition) (arg ε p w)
          * ((Lε ε)⁻¹ * ‖w - p‖⁻¹) ^ 2 : ℝ) : ℂ) := by
  have hin : ∀ v : ℂ, (fun z => fderiv ℝ (cut1C ε p) z v)
      = fun z => ((fderiv ℝ (cut1 ε p) z v : ℝ) : ℂ) :=
    fun v => funext fun z => fderiv_cut1C_apply h0 h1 p z v
  have hdin : ∀ v : ℂ, DifferentiableAt ℝ (fun z => fderiv ℝ (cut1 ε p) z v) w := fun v =>
    (((cut1_contDiff h0 h1 p).contDiffAt.fderiv_right (m := 1)
      (by simpa using (WithTop.coe_le_coe.mpr (le_top : (1 + 1 : ℕ∞) ≤ ⊤)))).clm_apply
        contDiffAt_const).differentiableAt one_ne_zero
  have houter : ∀ v : ℂ, fderiv ℝ (fun z => ((fderiv ℝ (cut1 ε p) z v : ℝ) : ℂ)) w v
      = ((fderiv ℝ (fun z => fderiv ℝ (cut1 ε p) z v) w v : ℝ) : ℂ) := by
    intro v
    have hc : (fun z => ((fderiv ℝ (cut1 ε p) z v : ℝ) : ℂ))
        = ⇑Complex.ofRealCLM ∘ fun z => fderiv ℝ (cut1 ε p) z v := rfl
    rw [hc, fderiv_comp w Complex.ofRealCLM.differentiableAt (hdin v),
      ContinuousLinearMap.fderiv]
    rfl
  simp only [laplacian]
  rw [hin 1, hin Complex.I, houter 1, houter Complex.I, ← Complex.ofReal_add, lapR_cut1 hw]

/-! ### Vanishing off the annulus -/

/-- The Laplacian of an eventually-constant function vanishes. -/
lemma laplacian_eq_zero_of_eventually_const {f : ℂ → ℂ} {w : ℂ} {c : ℂ}
    (hev : f =ᶠ[nhds w] fun _ => c) : laplacian f w = 0 := by
  have h1 : ∀ v : ℂ, (fun z => fderiv ℝ f z v) =ᶠ[nhds w] fun _ => (0 : ℂ) := by
    intro v
    filter_upwards [hev.eventually_nhds] with z hz
    have hz' : f =ᶠ[nhds z] fun _ => c := hz
    rw [hz'.fderiv_eq, fderiv_const_apply]
    simp
  simp only [laplacian]
  rw [(h1 1).fderiv_eq, (h1 Complex.I).fderiv_eq]
  simp

lemma laplacian_cut1C_inner {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {p w : ℂ}
    (hw : ‖w - p‖ < ε ^ 2) : laplacian (cut1C ε p) w = 0 := by
  refine laplacian_eq_zero_of_eventually_const (c := 0) ?_
  have hopen : IsOpen {z : ℂ | ‖z - p‖ < ε ^ 2} :=
    isOpen_lt (Continuous.norm (continuous_id.sub continuous_const)) continuous_const
  filter_upwards [hopen.mem_nhds hw] with z hz
  simp only [cut1C, cut1_eq_zero h0 h1 (le_of_lt hz), Complex.ofReal_zero]

lemma laplacian_cut1C_outer {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {p w : ℂ}
    (hw : ε < ‖w - p‖) : laplacian (cut1C ε p) w = 0 := by
  refine laplacian_eq_zero_of_eventually_const (c := 1) ?_
  have hopen : IsOpen {z : ℂ | ε < ‖z - p‖} :=
    isOpen_lt continuous_const (Continuous.norm (continuous_id.sub continuous_const))
  filter_upwards [hopen.mem_nhds hw] with z hz
  simp only [cut1C, cut1_eq_one h0 h1 (le_of_lt hz), Complex.ofReal_one]

/-! ### The pointwise bound and the O(1/L) integral -/

/-- The radial dominator: `Mψ₂/(Lr)²` on `[ε², ε]`, zero elsewhere. -/
def lapDom (ε : ℝ) (r : ℝ) : ℝ :=
  Set.indicator (Set.Icc (ε ^ 2) ε) (fun r => Mψ₂ * ((Lε ε)⁻¹ * r⁻¹) ^ 2) r

lemma lapDom_nonneg (ε r : ℝ) : 0 ≤ lapDom ε r := by
  unfold lapDom
  by_cases h : r ∈ Set.Icc (ε ^ 2) ε
  · rw [Set.indicator_of_mem h]
    have := Mψ₂_nonneg
    positivity
  · rw [Set.indicator_of_notMem h]

/-- **Pointwise domination**: `‖Δ(cut1C)‖ ≤ lapDom ε ‖w−p‖` everywhere. -/
lemma norm_laplacian_cut1C_le {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (p w : ℂ) :
    ‖laplacian (cut1C ε p) w‖ ≤ lapDom ε ‖w - p‖ := by
  by_cases hmem : ‖w - p‖ ∈ Set.Icc (ε ^ 2) ε
  · have hw : w ≠ p := by
      intro h; subst h
      simp only [sub_self, norm_zero] at hmem
      nlinarith [hmem.1, pow_pos h0 2]
    rw [laplacian_cut1C_eq h0 h1 hw]
    unfold lapDom
    rw [Set.indicator_of_mem hmem, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hL := (Lε_pos h0 h1).le
    have h2 : |((Lε ε)⁻¹ * ‖w - p‖⁻¹) ^ 2| = ((Lε ε)⁻¹ * ‖w - p‖⁻¹) ^ 2 :=
      abs_of_nonneg (by positivity)
    rw [h2]
    exact mul_le_mul_of_nonneg_right (abs_deriv2_smoothTransition_le _) (by positivity)
  · rcases not_and_or.mp (Set.mem_Icc.not.mp hmem) with h | h
    · rw [laplacian_cut1C_inner h0 h1 (not_le.mp h)]
      simpa using lapDom_nonneg ε ‖w - p‖
    · rw [laplacian_cut1C_outer h0 h1 (not_le.mp h)]
      simpa using lapDom_nonneg ε ‖w - p‖

lemma lapDom_le_const {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (r : ℝ) :
    lapDom ε r ≤ Mψ₂ * ((Lε ε)⁻¹ * (ε ^ 2)⁻¹) ^ 2 := by
  unfold lapDom
  by_cases h : r ∈ Set.Icc (ε ^ 2) ε
  · rw [Set.indicator_of_mem h]
    have hε2 : 0 < ε ^ 2 := pow_pos h0 2
    have hr0 : 0 < r := lt_of_lt_of_le hε2 h.1
    have hL : 0 < Lε ε := Lε_pos h0 h1
    gcongr
    · exact Mψ₂_nonneg
    · exact h.1
  · rw [Set.indicator_of_notMem h]
    have := Mψ₂_nonneg
    have hL := (Lε_pos h0 h1).le
    positivity

/-- The dominator (as a function of `w`) is integrable: bounded, supported in a ball. -/
lemma integrable_lapDom_comp {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (p : ℂ) :
    Integrable (fun w : ℂ => lapDom ε ‖w - p‖) := by
  have hmeas : Measurable fun w : ℂ => lapDom ε ‖w - p‖ := by
    have hbase : Measurable fun w : ℂ => ‖w - p‖ := (measurable_id.sub_const p).norm
    have hind : Measurable (lapDom ε) :=
      Measurable.indicator (by fun_prop) measurableSet_Icc
    exact hind.comp hbase
  refine Integrable.mono' (g := fun w : ℂ =>
    Set.indicator (Metric.closedBall p ε) (fun _ => Mψ₂ * ((Lε ε)⁻¹ * (ε ^ 2)⁻¹) ^ 2) w)
    ?_ hmeas.aestronglyMeasurable ?_
  · rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const measure_closedBall_lt_top.ne
  · refine Filter.Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (lapDom_nonneg _ _)]
    by_cases hball : w ∈ Metric.closedBall p ε
    · rw [Set.indicator_of_mem hball]
      exact lapDom_le_const h0 h1 _
    · rw [Set.indicator_of_notMem hball]
      unfold lapDom
      rw [Set.indicator_of_notMem]
      intro hmem
      exact hball (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hmem.2))

/-- The 1-D radial integral: `∫_{Ioi 0} y · lapDom ε y dy = Mψ₂/L`. -/
lemma integral_smul_lapDom {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    ∫ y in Set.Ioi (0 : ℝ), y • lapDom ε y = Mψ₂ * (Lε ε)⁻¹ := by
  have hε2 : 0 < ε ^ 2 := pow_pos h0 2
  have hL : 0 < Lε ε := Lε_pos h0 h1
  have hε2ε : ε ^ 2 ≤ ε := by nlinarith
  have hsub : Set.Icc (ε ^ 2) ε ⊆ Set.Ioi (0 : ℝ) := fun y hy => lt_of_lt_of_le hε2 hy.1
  have hind : (fun y : ℝ => y • lapDom ε y)
      = Set.indicator (Set.Icc (ε ^ 2) ε) (fun y => Mψ₂ * (Lε ε)⁻¹ ^ 2 * y⁻¹) := by
    funext y
    unfold lapDom
    by_cases h : y ∈ Set.Icc (ε ^ 2) ε
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, smul_eq_mul]
      have hy0 : 0 < y := lt_of_lt_of_le hε2 h.1
      field_simp
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, smul_eq_mul, mul_zero]
  rw [hind, setIntegral_indicator measurableSet_Icc,
    Set.inter_eq_right.mpr hsub, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hε2ε, intervalIntegral.integral_const_mul,
    integral_inv (by
      rw [Set.uIcc_of_le hε2ε]
      intro hmem
      exact absurd hmem.1 (not_le.mpr hε2))]
  have hlog : Real.log (ε / ε ^ 2) = Lε ε := by
    rw [show ε / ε ^ 2 = ε⁻¹ by field_simp, Real.log_inv]
    rfl
  rw [hlog]
  field_simp

/-- The integral estimate: `∫ ‖Δ(cut1C ε p)‖ ≤ 2π·Mψ₂/L`. -/
theorem integral_norm_laplacian_cut1C_le {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (p : ℂ) :
    ∫ w : ℂ, ‖laplacian (cut1C ε p) w‖ ≤ 2 * π * Mψ₂ * (Lε ε)⁻¹ := by
  have hcont : Continuous fun w : ℂ => laplacian (cut1C ε p) w := by
    rw [continuous_iff_continuousAt]
    exact fun w => laplacian_continuousAt (cut1C_contDiff h0 h1 p).contDiffAt
  have hint : Integrable fun w : ℂ => ‖laplacian (cut1C ε p) w‖ := by
    refine Integrable.mono' (integrable_lapDom_comp h0 h1 p)
      hcont.norm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun w => by
      rw [norm_norm]; exact norm_laplacian_cut1C_le h0 h1 p w
  have hmono : ∫ w : ℂ, ‖laplacian (cut1C ε p) w‖ ≤ ∫ w : ℂ, lapDom ε ‖w - p‖ :=
    integral_mono hint (integrable_lapDom_comp h0 h1 p)
      (fun w => norm_laplacian_cut1C_le h0 h1 p w)
  refine hmono.trans (le_of_eq ?_)
  have htrans : ∫ w : ℂ, lapDom ε ‖w - p‖ = ∫ w : ℂ, lapDom ε ‖w‖ :=
    integral_sub_right_eq_self (fun w : ℂ => lapDom ε ‖w‖) p
  rw [htrans, integral_fun_norm_addHaar (μ := (volume : Measure ℂ)) (lapDom ε)]
  rw [Complex.finrank_real_complex]
  have hvol : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    rw [Measure.real, Complex.volume_ball]
    simp
  rw [hvol]
  have hrad : ∫ y in Set.Ioi (0 : ℝ), y ^ (2 - 1) • lapDom ε y = Mψ₂ * (Lε ε)⁻¹ := by
    simpa using integral_smul_lapDom h0 h1
  rw [hrad]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

end KsIndex.CutLaplacian
