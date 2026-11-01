module

/-
KsIndexLean — SlitCutoffGrad: gradient, ground-state and area bounds for slit cutoffs.

The estimates that feed the collar bound `CollarBound.Qd_cut_collar` for `χ = cutSlit k δ c`
with collar `S_δ = {1 − 2δ ≤ re² + im²}`:

* `cutSlit_grad_bound` — `|∂₁χ| + |∂_I χ| ≤ 8Mψ/δ + 2kMψ/c` on `‖w‖ ≤ 1` (chain rule through
  the two `smoothTransition` profiles; `Mψ` is the global bound on `ψ'`);
* `cutSlit_off_collar` — off the collar, `χ ≡ 1` locally, so `fderiv χ = 0`;
* `groundC_collar_le` — `‖groundC‖ ≤ κ(2k−2)·2δ` on the collar (linear vanishing);
* `abs_groundC_le` — `‖groundC‖ ≤ κ` globally, and
* `volume_real_collar_le` — `vol(disk ∩ S_δ) ≤ 2πδ` (the annulus, for `δ ≤ ½`).
-/
public import KsIndexLean.SlitCutoff
public import KsIndexLean.GroundDisk
public import KsIndexLean.CutoffContinuity

@[expose] public section


noncomputable section

open Complex MeasureTheory Set Filter
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.Radial KsIndex.PunctureCutoff
open scoped ContDiff

namespace KsIndex.SingleDisk

variable {k : ℕ}

/-! ### Derivative of the chart variable `re² + im²` -/

lemma hasFDerivAt_sqBase (w : ℂ) :
    HasFDerivAt (fun w : ℂ => w.re ^ 2 + w.im ^ 2)
      ((2 * w.re) • (Complex.reCLM : ℂ →L[ℝ] ℝ)
        + (2 * w.im) • (Complex.imCLM : ℂ →L[ℝ] ℝ)) w := by
  have h := ((Complex.reCLM.hasFDerivAt (x := w)).pow 2).add
    ((Complex.imCLM.hasFDerivAt (x := w)).pow 2)
  have e : (((2 : ℕ) • (Complex.reCLM : ℂ →L[ℝ] ℝ) w ^ (2 - 1))
        • (Complex.reCLM : ℂ →L[ℝ] ℝ)
      + ((2 : ℕ) • (Complex.imCLM : ℂ →L[ℝ] ℝ) w ^ (2 - 1))
        • (Complex.imCLM : ℂ →L[ℝ] ℝ))
      = ((2 * w.re) • (Complex.reCLM : ℂ →L[ℝ] ℝ)
        + (2 * w.im) • (Complex.imCLM : ℂ →L[ℝ] ℝ)) := by
    ext v
    simp [smul_eq_mul]
  rw [e] at h
  exact h

lemma sqBase_deriv_apply (w v : ℂ) :
    (((2 * w.re) • (Complex.reCLM : ℂ →L[ℝ] ℝ)
        + (2 * w.im) • (Complex.imCLM : ℂ →L[ℝ] ℝ)) : ℂ →L[ℝ] ℝ) v
      = 2 * w.re * v.re + 2 * w.im * v.im := by
  simp [smul_eq_mul]

/-! ### The gradient bound for `cutSlit` -/

lemma norm_reCLM_le : ‖(Complex.reCLM : ℂ →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [Complex.reCLM_apply, Real.norm_eq_abs, one_mul]
    exact Complex.abs_re_le_norm z

lemma norm_imCLM_le : ‖(Complex.imCLM : ℂ →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
    rw [Complex.imCLM_apply, Real.norm_eq_abs, one_mul]
    exact Complex.abs_im_le_norm z

/-- **The cut-off gradient bound on the closed disk**:
`|∂₁ cutSlit| + |∂_I cutSlit| ≤ 8Mψ/δ + 2kMψ/c`. -/
lemma cutSlit_grad_bound {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    |fderiv ℝ (cutSlit k δ c) w 1| + |fderiv ℝ (cutSlit k δ c) w I|
      ≤ 8 * Mψ / δ + 2 * (k : ℝ) * Mψ / c := by
  have hψdiff : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
  -- the radial factor, written multiplicatively
  set LA0 := ((2 * w.re) • (Complex.reCLM : ℂ →L[ℝ] ℝ)
    + (2 * w.im) • (Complex.imCLM : ℂ →L[ℝ] ℝ)) with hLA0
  have haRadEq : aRad δ = fun z : ℂ =>
      Real.smoothTransition ((1 / δ) * (z.re ^ 2 + z.im ^ 2 - (1 - 2 * δ))) := by
    funext z
    rw [aRad, div_eq_inv_mul, one_div]
  set tA := (1 / δ) * (w.re ^ 2 + w.im ^ 2 - (1 - 2 * δ)) with htA
  have hArg : HasFDerivAt (fun z : ℂ => (1 / δ) * (z.re ^ 2 + z.im ^ 2 - (1 - 2 * δ)))
      ((1 / δ) • LA0) w := ((hasFDerivAt_sqBase w).sub_const (1 - 2 * δ)).const_mul (1 / δ)
  have hA : HasFDerivAt (aRad δ)
      ((deriv Real.smoothTransition tA) • ((1 / δ) • LA0)) w := by
    rw [haRadEq]
    have h := (hψdiff tA).hasDerivAt.comp_hasFDerivAt w hArg
    simpa [Function.comp_def] using h
  -- the angular factor, written multiplicatively
  have hbAngEq : bAng k c = fun z : ℂ =>
      Real.smoothTransition ((1 / c) * (2 * c - (z ^ k).re)) := by
    funext z
    rw [bAng, div_eq_inv_mul, one_div]
  have hpow := ((hasDerivAt_pow k w).hasFDerivAt).restrictScalars ℝ
  have hre := (Complex.reCLM.hasFDerivAt (x := w ^ k)).comp w hpow
  have hre' : HasFDerivAt (fun z : ℂ => (z ^ k).re)
      ((Complex.reCLM : ℂ →L[ℝ] ℝ).comp
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
          ((k : ℂ) * w ^ (k - 1))).restrictScalars ℝ)) w := hre
  set LB0 := (Complex.reCLM : ℂ →L[ℝ] ℝ).comp
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      ((k : ℂ) * w ^ (k - 1))).restrictScalars ℝ) with hLB0
  have hBrg : HasFDerivAt (fun z : ℂ => (1 / c) * (2 * c - (z ^ k).re))
      ((1 / c) • (-LB0)) w := (hre'.const_sub (2 * c)).const_mul (1 / c)
  set tB := (1 / c) * (2 * c - (w ^ k).re) with htB
  have hB : HasFDerivAt (bAng k c)
      ((deriv Real.smoothTransition tB) • ((1 / c) • (-LB0))) w := by
    rw [hbAngEq]
    have h := (hψdiff tB).hasDerivAt.comp_hasFDerivAt w hBrg
    simpa [Function.comp_def] using h
  -- the product and the cut-off
  have hprod := hA.mul hB
  have hcut : HasFDerivAt (cutSlit k δ c)
      (-(aRad δ w • ((deriv Real.smoothTransition tB) • ((1 / c) • (-LB0)))
        + bAng k c w • ((deriv Real.smoothTransition tA) • ((1 / δ) • LA0)))) w := by
    have h := hprod.const_sub 1
    exact h
  -- norm bounds on the pieces
  have hψA := abs_deriv_smoothTransition_le tA
  have hψB := abs_deriv_smoothTransition_le tB
  have hwre : |w.re| ≤ 1 := le_trans (Complex.abs_re_le_norm w) hw
  have hwim : |w.im| ≤ 1 := le_trans (Complex.abs_im_le_norm w) hw
  have hLA0n : ‖LA0‖ ≤ 4 := by
    rw [hLA0]
    calc ‖(2 * w.re) • (Complex.reCLM : ℂ →L[ℝ] ℝ) + (2 * w.im) • Complex.imCLM‖
        ≤ ‖(2 * w.re) • (Complex.reCLM : ℂ →L[ℝ] ℝ)‖ + ‖(2 * w.im) • (Complex.imCLM : ℂ →L[ℝ] ℝ)‖ :=
          norm_add_le _ _
      _ = |2 * w.re| * ‖(Complex.reCLM : ℂ →L[ℝ] ℝ)‖ + |2 * w.im| * ‖(Complex.imCLM : ℂ →L[ℝ] ℝ)‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 2 * 1 + 2 * 1 := by
          refine add_le_add (mul_le_mul ?_ norm_reCLM_le (norm_nonneg _) (by norm_num))
            (mul_le_mul ?_ norm_imCLM_le (norm_nonneg _) (by norm_num))
          · rw [abs_mul, abs_two]
            linarith [hwre]
          · rw [abs_mul, abs_two]
            linarith [hwim]
      _ = 4 := by norm_num
  have hLB0n : ‖LB0‖ ≤ (k : ℝ) := by
    rw [hLB0]
    refine ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg k) fun v => ?_
    have happ : ((Complex.reCLM : ℂ →L[ℝ] ℝ).comp
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
          ((k : ℂ) * w ^ (k - 1))).restrictScalars ℝ)) v
        = (v * ((k : ℂ) * w ^ (k - 1))).re := by
      simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    rw [happ, Real.norm_eq_abs]
    calc |(v * ((k : ℂ) * w ^ (k - 1))).re| ≤ ‖v * ((k : ℂ) * w ^ (k - 1))‖ :=
          Complex.abs_re_le_norm _
      _ = ‖v‖ * ((k : ℝ) * ‖w‖ ^ (k - 1)) := by
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
      _ ≤ ‖v‖ * ((k : ℝ) * 1) := by
          have h1 : ‖w‖ ^ (k - 1) ≤ 1 := pow_le_one₀ (norm_nonneg w) hw
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k)) (norm_nonneg v)
      _ = (k : ℝ) * ‖v‖ := by ring
  have hDcut : ‖fderiv ℝ (cutSlit k δ c) w‖ ≤ 4 * Mψ / δ + (k : ℝ) * Mψ / c := by
    rw [hcut.fderiv, norm_neg]
    obtain ⟨hA0, hA1⟩ := aRad_mem_Icc δ w
    obtain ⟨hB0, hB1⟩ := bAng_mem_Icc k c w
    have hBn : ‖aRad δ w • ((deriv Real.smoothTransition tB) • ((1 / c) • (-LB0)))‖
        ≤ (k : ℝ) * Mψ / c := by
      rw [norm_smul, norm_smul, norm_smul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hA0, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / c)]
      have inner1 : 1 / c * ‖LB0‖ ≤ 1 / c * (k : ℝ) :=
        mul_le_mul_of_nonneg_left hLB0n (by positivity)
      have inner2 : |deriv Real.smoothTransition tB| * (1 / c * ‖LB0‖)
          ≤ Mψ * (1 / c * (k : ℝ)) :=
        mul_le_mul hψB inner1 (by positivity) Mψ_nonneg
      calc aRad δ w * (|deriv Real.smoothTransition tB| * (1 / c * ‖LB0‖))
          ≤ 1 * (Mψ * (1 / c * (k : ℝ))) :=
            mul_le_mul hA1 inner2 (by positivity) zero_le_one
        _ = (k : ℝ) * Mψ / c := by ring
    have hAn : ‖bAng k c w • ((deriv Real.smoothTransition tA) • ((1 / δ) • LA0))‖
        ≤ 4 * Mψ / δ := by
      rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hB0, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / δ)]
      have inner1 : 1 / δ * ‖LA0‖ ≤ 1 / δ * 4 :=
        mul_le_mul_of_nonneg_left hLA0n (by positivity)
      have inner2 : |deriv Real.smoothTransition tA| * (1 / δ * ‖LA0‖)
          ≤ Mψ * (1 / δ * 4) :=
        mul_le_mul hψA inner1 (by positivity) Mψ_nonneg
      calc bAng k c w * (|deriv Real.smoothTransition tA| * (1 / δ * ‖LA0‖))
          ≤ 1 * (Mψ * (1 / δ * 4)) :=
            mul_le_mul hB1 inner2 (by positivity) zero_le_one
        _ = 4 * Mψ / δ := by ring
    calc ‖aRad δ w • ((deriv Real.smoothTransition tB) • ((1 / c) • (-LB0)))
        + bAng k c w • ((deriv Real.smoothTransition tA) • ((1 / δ) • LA0))‖
        ≤ ‖aRad δ w • ((deriv Real.smoothTransition tB) • ((1 / c) • (-LB0)))‖
          + ‖bAng k c w • ((deriv Real.smoothTransition tA) • ((1 / δ) • LA0))‖ :=
          norm_add_le _ _
      _ ≤ (k : ℝ) * Mψ / c + 4 * Mψ / δ := add_le_add hBn hAn
      _ = 4 * Mψ / δ + (k : ℝ) * Mψ / c := by ring
  -- components from the operator norm
  have hc1 : |fderiv ℝ (cutSlit k δ c) w 1| ≤ 4 * Mψ / δ + (k : ℝ) * Mψ / c := by
    rw [← Real.norm_eq_abs]
    have h := (fderiv ℝ (cutSlit k δ c) w).le_opNorm 1
    rw [norm_one, mul_one] at h
    exact h.trans hDcut
  have hcI : |fderiv ℝ (cutSlit k δ c) w I| ≤ 4 * Mψ / δ + (k : ℝ) * Mψ / c := by
    rw [← Real.norm_eq_abs]
    have h := (fderiv ℝ (cutSlit k δ c) w).le_opNorm I
    rw [Complex.norm_I, mul_one] at h
    exact h.trans hDcut
  calc |fderiv ℝ (cutSlit k δ c) w 1| + |fderiv ℝ (cutSlit k δ c) w I|
      ≤ (4 * Mψ / δ + (k : ℝ) * Mψ / c) + (4 * Mψ / δ + (k : ℝ) * Mψ / c) :=
        add_le_add hc1 hcI
    _ = 8 * Mψ / δ + 2 * (k : ℝ) * Mψ / c := by ring

/-! ### Off the collar the cut-off is locally `≡ 1` -/

/-- Off the collar (`re² + im² < 1 − 2δ`) the cut-off is `1` with vanishing derivative. -/
lemma cutSlit_off_collar {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) {w : ℂ}
    (hlt : w.re ^ 2 + w.im ^ 2 < 1 - 2 * δ) :
    cutSlit k δ c w = 1 ∧ fderiv ℝ (cutSlit k δ c) w = 0 := by
  refine ⟨cutSlit_one hδ hc (Or.inl hlt.le), ?_⟩
  have hopen : IsOpen {z : ℂ | z.re ^ 2 + z.im ^ 2 < 1 - 2 * δ} := by
    have : Continuous fun z : ℂ => z.re ^ 2 + z.im ^ 2 :=
      ((Complex.continuous_re.pow 2).add (Complex.continuous_im.pow 2))
    exact isOpen_lt this continuous_const
  have hev : cutSlit k δ c =ᶠ[nhds w] fun _ => (1 : ℝ) := by
    filter_upwards [hopen.mem_nhds hlt] with z hz
    exact cutSlit_one hδ hc (Or.inl (le_of_lt hz))
  rw [hev.fderiv_eq]
  exact fderiv_const_apply 1

/-! ### The ground state on the collar and globally -/

/-- Linear smallness of the ground state on the collar. -/
lemma groundC_collar_le (hk2 : 2 ≤ k) {δ : ℝ} {w : ℂ} (hw : ‖w‖ < 1)
    (hS : 1 - 2 * δ ≤ w.re ^ 2 + w.im ^ 2) :
    ‖groundC k w‖ ≤ kap k * ((2 * k - 2 : ℕ) : ℝ) * (2 * δ) := by
  have hk1 : 1 ≤ k := by omega
  have hκ : 0 < kap k := kap_pos hk2
  have hn : ‖groundC k w‖ = |gRad k 0 ‖w‖| := by
    rw [groundC, Complex.norm_real, Real.norm_eq_abs, groundR_eq hk1]
  have hpos : 0 ≤ gRad k 0 ‖w‖ := (gRad_zero_pos hk2 (norm_nonneg w) hw).le
  rw [hn, abs_of_nonneg hpos]
  have hlin := gRad_zero_le_lin hk2 (norm_nonneg w) hw.le
  have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := norm_sq_eq w
  have h2δ : 1 - ‖w‖ ≤ 2 * δ := by
    have h1 : 1 - ‖w‖ ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w, hw.le]
    rw [hsq] at h1
    linarith
  calc gRad k 0 ‖w‖ ≤ kap k * ((2 * k - 2 : ℕ) : ℝ) * (1 - ‖w‖) := hlin
    _ ≤ kap k * ((2 * k - 2 : ℕ) : ℝ) * (2 * δ) :=
        mul_le_mul_of_nonneg_left h2δ (mul_nonneg hκ.le (Nat.cast_nonneg _))

/-- The ground state is globally bounded by `κ`. -/
lemma abs_groundC_le (hk2 : 2 ≤ k) (w : ℂ) : ‖groundC k w‖ ≤ kap k := by
  have hk1 : 1 ≤ k := by omega
  have hκ : 0 < kap k := kap_pos hk2
  rw [groundC, Complex.norm_real, Real.norm_eq_abs, groundR_eq hk1, gRad]
  set s := ‖w‖ ^ (2 * k - 2) with hs
  have hs0 : 0 ≤ s := pow_even_nonneg k ‖w‖
  have hnum : ((0 : ℕ) : ℝ) + kap k + (((0 : ℕ) : ℝ) - kap k) * s = kap k * (1 - s) := by
    push_cast
    ring
  rw [abs_div, hnum, abs_mul, abs_of_pos hκ, abs_of_pos (denom_pos k ‖w‖)]
  rw [div_le_iff₀ (denom_pos k ‖w‖)]
  have habs : |1 - s| ≤ 1 + s := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith [habs, hκ.le]

/-! ### The collar volume -/

/-- The collar has area at most `2πδ`. -/
lemma volume_real_collar_le {δ : ℝ} (hδ : 0 < δ) (hhalf : δ ≤ 1 / 2) :
    (volume : Measure ℂ).real (disk ∩ {w : ℂ | 1 - 2 * δ ≤ w.re ^ 2 + w.im ^ 2})
      ≤ 2 * Real.pi * δ := by
  set S := {w : ℂ | 1 - 2 * δ ≤ w.re ^ 2 + w.im ^ 2} with hSdef
  set s := Real.sqrt (1 - 2 * δ) with hsdef
  have hs0 : (0 : ℝ) ≤ 1 - 2 * δ := by linarith
  have hdisj : Disjoint (disk ∩ S) (Metric.ball (0 : ℂ) s) := by
    rw [Set.disjoint_left]
    rintro w ⟨-, hwS⟩ hwb
    rw [Metric.mem_ball, dist_zero_right] at hwb
    have h2 : ‖w‖ ^ 2 < s ^ 2 := by
      have := Real.sqrt_nonneg (1 - 2 * δ)
      nlinarith [norm_nonneg w]
    rw [Real.sq_sqrt hs0] at h2
    rw [Set.mem_ofPred_eq, ← norm_sq_eq] at hwS
    linarith
  have hsub : (disk ∩ S) ∪ Metric.ball (0 : ℂ) s ⊆ disk := by
    rintro w (⟨hw, -⟩ | hw)
    · exact hw
    · rw [Metric.mem_ball, dist_zero_right] at hw
      rw [mem_disk_iff]
      calc ‖w‖ < s := hw
        _ ≤ 1 := by
            rw [show (1 : ℝ) = Real.sqrt 1 by simp]
            exact Real.sqrt_le_sqrt (by linarith)
  have hmeas : volume ((disk ∩ S) ∪ Metric.ball (0 : ℂ) s)
      = volume (disk ∩ S) + volume (Metric.ball (0 : ℂ) s) :=
    measure_union hdisj measurableSet_ball
  have hle : volume (disk ∩ S) + volume (Metric.ball (0 : ℂ) s) ≤ volume disk := by
    rw [← hmeas]
    exact measure_mono hsub
  have hfin : volume disk ≠ ⊤ := (measure_ball_lt_top).ne
  have hfin1 : volume (disk ∩ S) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfin)).ne
  have hfin2 : volume (Metric.ball (0 : ℂ) s) ≠ ⊤ := (measure_ball_lt_top).ne
  have hball : (volume : Measure ℂ).real (Metric.ball (0 : ℂ) s)
      = Real.pi * (1 - 2 * δ) := by
    rw [Measure.real, Complex.volume_ball]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    rw [Real.sq_sqrt hs0]
    simp [NNReal.coe_real_pi]
    ring
  have hreal : (volume : Measure ℂ).real (disk ∩ S)
      + (volume : Measure ℂ).real (Metric.ball (0 : ℂ) s)
      ≤ (volume : Measure ℂ).real disk := by
    rw [Measure.real, Measure.real, Measure.real, ← ENNReal.toReal_add hfin1 hfin2]
    exact ENNReal.toReal_mono hfin hle
  rw [KsIndex.CutoffContinuity.volume_real_disk, hball] at hreal
  linarith

/-! ### The cut region: off-`S` vanishing, measurability, area -/

/-- The region where `cutSlit` may differ from `1`: the collar intersected with
the slit sector. This set supplies `S` to `Qd_cut_collar`, retaining the angular
restriction needed for the witness estimate. -/
def cutS (k : ℕ) (δ c : ℝ) : Set ℂ :=
  {z : ℂ | 1 - 2 * δ ≤ z.re ^ 2 + z.im ^ 2 ∧ (z ^ k).re ≤ 2 * c}

lemma measurableSet_cutS (k : ℕ) (δ c : ℝ) : MeasurableSet (cutS k δ c) := by
  have h1 : Continuous fun z : ℂ => z.re ^ 2 + z.im ^ 2 :=
    (Complex.continuous_re.pow 2).add (Complex.continuous_im.pow 2)
  have h2 : Continuous fun z : ℂ => (z ^ k).re :=
    Complex.continuous_re.comp (continuous_pow k)
  exact ((isClosed_le continuous_const h1).inter (isClosed_le h2 continuous_const)).measurableSet

/-- Off the cut region — radially inside OR beyond the sector — the cut-off is `1` with
vanishing derivative: `Qd_cut_collar`'s `hout`. -/
lemma cutSlit_off_S {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) {w : ℂ}
    (hw : w ∉ cutS k δ c) :
    cutSlit k δ c w = 1 ∧ fderiv ℝ (cutSlit k δ c) w = 0 := by
  rw [cutS, Set.mem_setOf_eq, not_and_or, not_le, not_le] at hw
  rcases hw with h | h
  · exact cutSlit_off_collar hδ hc h
  · refine ⟨cutSlit_one hδ hc (Or.inr h.le), ?_⟩
    have hopen : IsOpen {z : ℂ | 2 * c < (z ^ k).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_pow k))
    have hev : cutSlit k δ c =ᶠ[nhds w] fun _ => (1 : ℝ) := by
      filter_upwards [hopen.mem_nhds h] with z hz
      exact cutSlit_one hδ hc (Or.inr (le_of_lt hz))
    rw [hev.fderiv_eq]
    exact fderiv_const_apply 1

/-- The cut region's area within the disk is at most the collar's: `≤ 2πδ`. -/
lemma volume_real_cutS_le {δ c : ℝ} (hδ : 0 < δ) (hhalf : δ ≤ 1 / 2) :
    (volume : Measure ℂ).real (disk ∩ cutS k δ c) ≤ 2 * Real.pi * δ := by
  refine le_trans ?_ (volume_real_collar_le hδ hhalf)
  refine measureReal_mono (Set.inter_subset_inter_right _ (fun z hz => hz.1)) ?_
  refine (lt_of_le_of_lt (measure_mono Set.inter_subset_left) ?_).ne
  exact measure_ball_lt_top

end KsIndex.SingleDisk

