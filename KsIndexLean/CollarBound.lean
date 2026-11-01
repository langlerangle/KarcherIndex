module

/-
Collar-localized cutoff estimates for the disk pairing.

`Bd_cutLeft_collar` bounds the change when only the left argument is multiplied
by a cutoff χ taking values in [0,1]. The cutoff equals one and has zero derivative
outside a measurable collar S. On disk ∩ S, m bounds ‖f‖ and G bounds the sum of
the absolute values of the two real directional derivatives of χ. With global
value and derivative bounds for f and g, and k ≥ 2, the estimate is

  ‖Bd (χf) g − Bd f g‖ ≤ (2 Df Dg + G m Dg + V̄ m Mg) vol(disk ∩ S),

where V̄ = 8(k−1)² bounds the potential. Hermitian symmetry gives `Qd_cut_collar`:

  |Qd (χf) − Qd f| ≤ 2 (2 Df (Df+mG) + G m (Df+mG) + V̄ m Mf) vol(disk ∩ S).

For families with uniform global bounds, m = O(δ), G = O(δ⁻¹), and collar volume
O(δ), these estimates yield an O(δ) error. The family-dependent bounds are inputs
to these estimates; this module does not construct a slit-cutoff family.
-/
public import KsIndexLean.CutoffContinuity

@[expose] public section


noncomputable section

open Complex MeasureTheory Set Filter
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SingleDiskBridge KsIndex.GradOrtho
  KsIndex.ModeDiag KsIndex.CutoffContinuity

namespace KsIndex.CollarBound

variable {k : ℕ}

/-! ### Operator norms from the two real components -/

/-- `‖L‖ ≤ ‖L 1‖ + ‖L I‖` for an `ℝ`-linear map on `ℂ`. -/
lemma opNorm_le_components {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : ℂ →L[ℝ] F) {a b : ℝ} (h1 : ‖L 1‖ ≤ a) (hI : ‖L I‖ ≤ b) : ‖L‖ ≤ a + b := by
  have ha : 0 ≤ a := le_trans (norm_nonneg _) h1
  have hb : 0 ≤ b := le_trans (norm_nonneg _) hI
  refine L.opNorm_le_bound (by linarith) fun v => ?_
  have hv : (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • I = v := by
    simp only [Complex.real_smul, mul_one]
    exact Complex.re_add_im v
  calc ‖L v‖ = ‖v.re • L 1 + v.im • L I‖ := by rw [← map_smul, ← map_smul, ← map_add, hv]
    _ ≤ ‖v.re • L 1‖ + ‖v.im • L I‖ := norm_add_le _ _
    _ = |v.re| * ‖L 1‖ + |v.im| * ‖L I‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖v‖ * a + ‖v‖ * b := add_le_add
        (mul_le_mul (Complex.abs_re_le_norm v) h1 (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (Complex.abs_im_le_norm v) hI (norm_nonneg _) (norm_nonneg _))
    _ = (a + b) * ‖v‖ := by ring

/-! ### The pointwise one-sided-cut expansions -/

/-- The exact expansion of the gradient cross density when only the LEFT argument is cut. -/
lemma gradInner_cutLeft_sub {χ : ℂ → ℝ} {f g : ℂ → ℂ} {w : ℂ}
    (hχ : DifferentiableAt ℝ χ w) (hf : DifferentiableAt ℝ f w) :
    gradInner (cutMul χ f) g w - gradInner f g w
      = ((χ w - 1 : ℝ) : ℂ) * gradInner f g w
        + ((fderiv ℝ χ w 1 : ℝ) : ℂ) * ((starRingEnd ℂ) (f w) * fderiv ℝ g w 1)
        + ((fderiv ℝ χ w I : ℝ) : ℂ) * ((starRingEnd ℂ) (f w) * fderiv ℝ g w I) := by
  simp only [gradInner, fderiv_cutMul_apply hχ hf, map_add, map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- The exact expansion of the potential cross density when only the LEFT argument is cut. -/
lemma potCross_cutLeft_sub (χ : ℂ → ℝ) (f g : ℂ → ℂ) (V : ℝ) (w : ℂ) :
    (V : ℂ) * (starRingEnd ℂ) (cutMul χ f w) * g w - (V : ℂ) * (starRingEnd ℂ) (f w) * g w
      = ((χ w - 1 : ℝ) : ℂ) * ((V : ℂ) * (starRingEnd ℂ) (f w) * g w) := by
  simp only [cutMul, map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-! ### The collar-localized bound, one-sided cut -/

/-- **Collar-localized cut-off continuity, LEFT cut**: if the cut-off is `≡ 1` with vanishing
derivative off the collar `S`, `‖f‖ ≤ m` and `|∂₁χ| + |∂_I χ| ≤ G` on the collar, then

  `‖Bd (χf) g − Bd f g‖ ≤ (2 Df Dg + G m Dg + 8(k−1)² m Mg) · vol(disk ∩ S)`. -/
theorem Bd_cutLeft_collar (hk : 2 ≤ k) {χ : ℂ → ℝ} {S : Set ℂ} (hS : MeasurableSet S)
    (hχd : ∀ w, DifferentiableAt ℝ χ w) (hχ0 : ∀ w, 0 ≤ χ w) (hχ1 : ∀ w, χ w ≤ 1)
    (hout : ∀ w ∈ disk, w ∉ S → χ w = 1 ∧ fderiv ℝ χ w = 0)
    {f g : ℂ → ℂ} {m G Mf Df Mg Dg : ℝ} (hm0 : 0 ≤ m) (hG0 : 0 ≤ G)
    (hf : ∀ w ∈ disk, DifferentiableAt ℝ f w) (hMf : ∀ w ∈ disk, ‖f w‖ ≤ Mf)
    (hDf : ∀ w ∈ disk, ‖fderiv ℝ f w‖ ≤ Df)
    (hg : ∀ w ∈ disk, DifferentiableAt ℝ g w) (hMg : ∀ w ∈ disk, ‖g w‖ ≤ Mg)
    (hDg : ∀ w ∈ disk, ‖fderiv ℝ g w‖ ≤ Dg)
    (hm : ∀ w ∈ disk ∩ S, ‖f w‖ ≤ m)
    (hG : ∀ w ∈ disk ∩ S, |fderiv ℝ χ w 1| + |fderiv ℝ χ w I| ≤ G) :
    ‖Bd k (cutMul χ f) g - Bd k f g‖
      ≤ (2 * (Df * Dg) + G * (m * Dg) + 8 * ((k : ℝ) - 1) ^ 2 * (m * Mg))
          * (volume : Measure ℂ).real (disk ∩ S) := by
  set C := 2 * (Df * Dg) + G * (m * Dg) + 8 * ((k : ℝ) - 1) ^ 2 * (m * Mg) with hC
  have h0d : (0 : ℂ) ∈ disk := by rw [mem_disk_iff]; simp
  have hMf0 : 0 ≤ Mf := le_trans (norm_nonneg _) (hMf 0 h0d)
  have hMg0 : 0 ≤ Mg := le_trans (norm_nonneg _) (hMg 0 h0d)
  have hDf0 : 0 ≤ Df := le_trans (norm_nonneg _) (hDf 0 h0d)
  have hDg0 : 0 ≤ Dg := le_trans (norm_nonneg _) (hDg 0 h0d)
  -- the cut function's own data
  have hfχ : ∀ w ∈ disk, DifferentiableAt ℝ (cutMul χ f) w := fun w hw =>
    (hasFDerivAt_cutMul (hχd w) (hf w hw)).differentiableAt
  have hMfχ : ∀ w ∈ disk, ‖cutMul χ f w‖ ≤ Mf := fun w hw => by
    unfold cutMul
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 w)]
    exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (hχ1 w)) (hMf w hw)
  have hDfχ : ∀ w ∈ disk, ‖fderiv ℝ (cutMul χ f) w‖ ≤ Df + m * G := by
    intro w hw
    rw [(hasFDerivAt_cutMul (hχd w) (hf w hw)).fderiv]
    have hstep : ‖(χ w : ℂ) • fderiv ℝ f w + f w • (Complex.ofRealCLM.comp (fderiv ℝ χ w))‖
        ≤ ‖(χ w : ℂ) • fderiv ℝ f w‖ + ‖f w • (Complex.ofRealCLM.comp (fderiv ℝ χ w))‖ :=
      norm_add_le _ _
    refine le_trans hstep ?_
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 w)]
    by_cases hwS : w ∈ S
    · have hcomp : ‖Complex.ofRealCLM.comp (fderiv ℝ χ w)‖ ≤ G := by
        refine le_trans (opNorm_le_components _ (a := |fderiv ℝ χ w 1|) (b := |fderiv ℝ χ w I|)
          ?_ ?_) (hG w ⟨hw, hwS⟩)
        · rw [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real,
            Real.norm_eq_abs]
        · rw [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real,
            Real.norm_eq_abs]
      have t1 : χ w * ‖fderiv ℝ f w‖ ≤ Df :=
        le_trans (mul_le_of_le_one_left (norm_nonneg _) (hχ1 w)) (hDf w hw)
      have t2 : ‖f w‖ * ‖Complex.ofRealCLM.comp (fderiv ℝ χ w)‖ ≤ m * G :=
        mul_le_mul (hm w ⟨hw, hwS⟩) hcomp (norm_nonneg _) hm0
      linarith
    · obtain ⟨-, h0⟩ := hout w hw hwS
      rw [h0, show (Complex.ofRealCLM.comp (0 : ℂ →L[ℝ] ℝ)) = 0 by ext v; simp]
      simp only [norm_zero]
      have t1 : χ w * ‖fderiv ℝ f w‖ ≤ Df :=
        le_trans (mul_le_of_le_one_left (norm_nonneg _) (hχ1 w)) (hDf w hw)
      nlinarith [mul_nonneg hm0 hG0]
  -- pointwise bound by the indicator
  have hpt : ∀ w ∈ disk,
      ‖(gradInner (cutMul χ f) g w - gradInner f g w)
        - (((potV k w : ℂ) * (starRingEnd ℂ) (cutMul χ f w) * g w)
            - ((potV k w : ℂ) * (starRingEnd ℂ) (f w) * g w))‖
        ≤ C * S.indicator (fun _ => (1 : ℝ)) w := by
    intro w hw
    by_cases hwS : w ∈ S
    · rw [Set.indicator_of_mem hwS, mul_one]
      have hmw := hm w ⟨hw, hwS⟩
      have hGw := hG w ⟨hw, hwS⟩
      have hgIb := norm_gradInner_le_of_bounded (hDf w hw) (hDg w hw)
      have hd1 : ‖fderiv ℝ g w 1‖ ≤ Dg := by
        have h := (fderiv ℝ g w).le_opNorm 1
        rw [norm_one, mul_one] at h
        exact h.trans (hDg w hw)
      have hdI : ‖fderiv ℝ g w I‖ ≤ Dg := by
        have h := (fderiv ℝ g w).le_opNorm I
        rw [Complex.norm_I, mul_one] at h
        exact h.trans (hDg w hw)
      have hchi1 : |χ w - 1| ≤ 1 := by
        rw [abs_of_nonpos (by linarith [hχ1 w])]
        linarith [hχ0 w]
      have e1 : ‖gradInner (cutMul χ f) g w - gradInner f g w‖
          ≤ 2 * (Df * Dg) + G * (m * Dg) := by
        rw [gradInner_cutLeft_sub (hχd w) (hf w hw)]
        have hX : ‖((χ w - 1 : ℝ) : ℂ) * gradInner f g w‖ ≤ 2 * (Df * Dg) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          refine le_trans (mul_le_mul hchi1 hgIb (norm_nonneg _) zero_le_one) ?_
          rw [one_mul]
        have hY : ‖((fderiv ℝ χ w 1 : ℝ) : ℂ) * ((starRingEnd ℂ) (f w) * fderiv ℝ g w 1)‖
            ≤ |fderiv ℝ χ w 1| * (m * Dg) := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
          exact mul_le_mul le_rfl
            (mul_le_mul hmw hd1 (norm_nonneg _) hm0) (by positivity) (abs_nonneg _)
        have hZ : ‖((fderiv ℝ χ w I : ℝ) : ℂ) * ((starRingEnd ℂ) (f w) * fderiv ℝ g w I)‖
            ≤ |fderiv ℝ χ w I| * (m * Dg) := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
          exact mul_le_mul le_rfl
            (mul_le_mul hmw hdI (norm_nonneg _) hm0) (by positivity) (abs_nonneg _)
        have hsum : |fderiv ℝ χ w 1| * (m * Dg) + |fderiv ℝ χ w I| * (m * Dg)
            ≤ G * (m * Dg) := by
          have := mul_le_mul_of_nonneg_right hGw (mul_nonneg hm0 hDg0)
          linarith [this]
        refine le_trans (norm_add₃_le) ?_
        linarith [hX, hY, hZ, hsum]
      have e2 : ‖((potV k w : ℂ) * (starRingEnd ℂ) (cutMul χ f w) * g w)
          - ((potV k w : ℂ) * (starRingEnd ℂ) (f w) * g w)‖
          ≤ 8 * ((k : ℝ) - 1) ^ 2 * (m * Mg) := by
        rw [potCross_cutLeft_sub]
        have hfact : ‖((χ w - 1 : ℝ) : ℂ) * ((potV k w : ℂ) * (starRingEnd ℂ) (f w) * g w)‖
            = |χ w - 1| * (potV k w * (‖f w‖ * ‖g w‖)) := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj,
            abs_of_nonneg (KsIndex.CutoffContinuity.potV_nonneg k w)]
          ring
        rw [hfact]
        have t1 : ‖f w‖ * ‖g w‖ ≤ m * Mg :=
          mul_le_mul hmw (hMg w hw) (norm_nonneg _) hm0
        have t2 : (0 : ℝ) ≤ ‖f w‖ * ‖g w‖ := by positivity
        have s1 : potV k w * (‖f w‖ * ‖g w‖) ≤ 8 * ((k : ℝ) - 1) ^ 2 * (m * Mg) :=
          mul_le_mul (potV_le hk (mem_disk_iff.mp hw).le) t1 t2 (by positivity)
        calc |χ w - 1| * (potV k w * (‖f w‖ * ‖g w‖))
            ≤ 1 * (potV k w * (‖f w‖ * ‖g w‖)) :=
              mul_le_mul_of_nonneg_right hchi1
                (mul_nonneg (KsIndex.CutoffContinuity.potV_nonneg k w) t2)
          _ = potV k w * (‖f w‖ * ‖g w‖) := one_mul _
          _ ≤ _ := s1
      refine le_trans (norm_sub_le _ _) ?_
      rw [hC]
      linarith [e1, e2]
    · obtain ⟨h1, h0⟩ := hout w hw hwS
      rw [Set.indicator_of_notMem hwS, mul_zero]
      have z1 : gradInner (cutMul χ f) g w - gradInner f g w = 0 := by
        rw [gradInner_cutLeft_sub (hχd w) (hf w hw), h1, h0]
        simp
      have z2 : ((potV k w : ℂ) * (starRingEnd ℂ) (cutMul χ f w) * g w)
          - ((potV k w : ℂ) * (starRingEnd ℂ) (f w) * g w) = 0 := by
        rw [potCross_cutLeft_sub, h1]
        simp
      rw [z1, z2, sub_zero, norm_zero]
  -- integrability of the four densities
  have hgI : IntegrableOn (gradInner f g) disk := integrableOn_gradInner_bounded hDf hDg
  have hgIχ : IntegrableOn (gradInner (cutMul χ f) g) disk :=
    integrableOn_gradInner_bounded hDfχ hDg
  have hpot : IntegrableOn (fun w => (potV k w : ℂ) * (starRingEnd ℂ) (f w) * g w) disk :=
    integrableOn_pot hk (continuousOn_of_diff hf) (continuousOn_of_diff hg) hMf hMg
  have hpotχ : IntegrableOn
      (fun w => (potV k w : ℂ) * (starRingEnd ℂ) (cutMul χ f w) * g w) disk :=
    integrableOn_pot hk (continuousOn_of_diff hfχ) (continuousOn_of_diff hg) hMfχ hMg
  -- the difference as one integral
  have hBd : Bd k (cutMul χ f) g - Bd k f g
      = ∫ w in disk, ((gradInner (cutMul χ f) g w - gradInner f g w)
          - (((potV k w : ℂ) * (starRingEnd ℂ) (cutMul χ f w) * g w)
              - ((potV k w : ℂ) * (starRingEnd ℂ) (f w) * g w))) := by
    have i1 : IntegrableOn (fun w => gradInner (cutMul χ f) g w - gradInner f g w) disk :=
      hgIχ.sub hgI
    have i2 : IntegrableOn (fun w => ((potV k w : ℂ) * (starRingEnd ℂ) (cutMul χ f w) * g w)
        - ((potV k w : ℂ) * (starRingEnd ℂ) (f w) * g w)) disk := hpotχ.sub hpot
    rw [integral_sub i1 i2, integral_sub hgIχ hgI, integral_sub hpotχ hpot]
    unfold Bd
    ring
  -- the indicator bound integrates to C · vol
  have hI1 : IntegrableOn (fun w => C * S.indicator (fun _ => (1 : ℝ)) w) disk :=
    ((integrableOn_const (C := (1 : ℝ)) (measure_ball_lt_top).ne).indicator hS).const_mul C
  rw [hBd]
  calc ‖∫ w in disk, ((gradInner (cutMul χ f) g w - gradInner f g w)
        - (((potV k w : ℂ) * (starRingEnd ℂ) (cutMul χ f w) * g w)
            - ((potV k w : ℂ) * (starRingEnd ℂ) (f w) * g w)))‖
      ≤ ∫ w in disk, C * S.indicator (fun _ => (1 : ℝ)) w := by
        refine norm_integral_le_of_norm_le hI1 ?_
        rw [ae_restrict_iff' measurableSet_disk]
        exact Eventually.of_forall hpt
    _ = C * (volume : Measure ℂ).real (disk ∩ S) := by
        rw [integral_const_mul, setIntegral_indicator hS, setIntegral_const, smul_eq_mul,
          mul_one]

/-! ### The diagonal corollary -/

/-- **Collar-localized energy continuity (diagonal)**:
`|Qd (χf) − Qd f| ≤ 2·(2 Df (Df+mG) + G m (Df+mG) + 8(k−1)² m Mf) · vol(disk ∩ S)`. -/
theorem Qd_cut_collar (hk : 2 ≤ k) {χ : ℂ → ℝ} {S : Set ℂ} (hS : MeasurableSet S)
    (hχd : ∀ w, DifferentiableAt ℝ χ w) (hχ0 : ∀ w, 0 ≤ χ w) (hχ1 : ∀ w, χ w ≤ 1)
    (hout : ∀ w ∈ disk, w ∉ S → χ w = 1 ∧ fderiv ℝ χ w = 0)
    {f : ℂ → ℂ} {m G Mf Df : ℝ} (hm0 : 0 ≤ m) (hG0 : 0 ≤ G)
    (hf : ∀ w ∈ disk, DifferentiableAt ℝ f w) (hMf : ∀ w ∈ disk, ‖f w‖ ≤ Mf)
    (hDf : ∀ w ∈ disk, ‖fderiv ℝ f w‖ ≤ Df)
    (hm : ∀ w ∈ disk ∩ S, ‖f w‖ ≤ m)
    (hG : ∀ w ∈ disk ∩ S, |fderiv ℝ χ w 1| + |fderiv ℝ χ w I| ≤ G) :
    |Qd k (cutMul χ f) - Qd k f|
      ≤ 2 * (2 * (Df * (Df + m * G)) + G * (m * (Df + m * G))
          + 8 * ((k : ℝ) - 1) ^ 2 * (m * Mf))
        * (volume : Measure ℂ).real (disk ∩ S) := by
  have h0d : (0 : ℂ) ∈ disk := by rw [mem_disk_iff]; simp
  have hMf0 : 0 ≤ Mf := le_trans (norm_nonneg _) (hMf 0 h0d)
  have hDf0 : 0 ≤ Df := le_trans (norm_nonneg _) (hDf 0 h0d)
  have hvol0 : 0 ≤ (volume : Measure ℂ).real (disk ∩ S) := by positivity
  -- the cut function's data (as the RIGHT argument)
  have hfχ : ∀ w ∈ disk, DifferentiableAt ℝ (cutMul χ f) w := fun w hw =>
    (hasFDerivAt_cutMul (hχd w) (hf w hw)).differentiableAt
  have hMfχ : ∀ w ∈ disk, ‖cutMul χ f w‖ ≤ Mf := fun w hw => by
    unfold cutMul
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 w)]
    exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (hχ1 w)) (hMf w hw)
  -- ‖fderiv (cutMul χ f)‖ ≤ Df + m G on the disk: re-derive as in Bd_cutLeft_collar
  have hDfχ : ∀ w ∈ disk, ‖fderiv ℝ (cutMul χ f) w‖ ≤ Df + m * G := by
    intro w hw
    rw [(hasFDerivAt_cutMul (hχd w) (hf w hw)).fderiv]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 w)]
    by_cases hwS : w ∈ S
    · have hcomp : ‖Complex.ofRealCLM.comp (fderiv ℝ χ w)‖ ≤ G := by
        refine le_trans (opNorm_le_components _ (a := |fderiv ℝ χ w 1|) (b := |fderiv ℝ χ w I|)
          ?_ ?_) (hG w ⟨hw, hwS⟩)
        · rw [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real,
            Real.norm_eq_abs]
        · rw [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real,
            Real.norm_eq_abs]
      have t1 : χ w * ‖fderiv ℝ f w‖ ≤ Df :=
        le_trans (mul_le_of_le_one_left (norm_nonneg _) (hχ1 w)) (hDf w hw)
      have t2 : ‖f w‖ * ‖Complex.ofRealCLM.comp (fderiv ℝ χ w)‖ ≤ m * G :=
        mul_le_mul (hm w ⟨hw, hwS⟩) hcomp (norm_nonneg _) hm0
      linarith
    · obtain ⟨-, h0⟩ := hout w hw hwS
      rw [h0, show (Complex.ofRealCLM.comp (0 : ℂ →L[ℝ] ℝ)) = 0 by ext v; simp]
      simp only [norm_zero]
      have t1 : χ w * ‖fderiv ℝ f w‖ ≤ Df :=
        le_trans (mul_le_of_le_one_left (norm_nonneg _) (hχ1 w)) (hDf w hw)
      nlinarith [mul_nonneg hm0 hG0]
  -- split the diagonal difference through the mixed term
  have hA := Bd_cutLeft_collar hk hS hχd hχ0 hχ1 hout hm0 hG0 hf hMf hDf
    hfχ hMfχ hDfχ hm hG (g := cutMul χ f)
  have hB := Bd_cutLeft_collar hk hS hχd hχ0 hχ1 hout hm0 hG0 hf hMf hDf
    hf hMf hDf hm hG (g := f)
  -- the right-cut difference via Hermitian symmetry
  have hBsym : ‖Bd k f (cutMul χ f) - Bd k f f‖ = ‖Bd k (cutMul χ f) f - Bd k f f‖ := by
    have h1 : Bd k f (cutMul χ f) - Bd k f f
        = (starRingEnd ℂ) (Bd k (cutMul χ f) f - Bd k f f) := by
      rw [map_sub, Bd_conj_symm, Bd_conj_symm]
    rw [h1, Complex.norm_conj]
  have htri : ‖Bd k (cutMul χ f) (cutMul χ f) - Bd k f f‖
      ≤ ‖Bd k (cutMul χ f) (cutMul χ f) - Bd k f (cutMul χ f)‖
        + ‖Bd k f (cutMul χ f) - Bd k f f‖ := by
    have hsplit : Bd k (cutMul χ f) (cutMul χ f) - Bd k f f
        = (Bd k (cutMul χ f) (cutMul χ f) - Bd k f (cutMul χ f))
          + (Bd k f (cutMul χ f) - Bd k f f) := by ring
    rw [hsplit]
    exact norm_add_le _ _
  -- convert to Qd
  have hQd : |Qd k (cutMul χ f) - Qd k f| = ‖Bd k (cutMul χ f) (cutMul χ f) - Bd k f f‖ := by
    rw [Bd_self_eq_Qd hk, Bd_self_eq_Qd hk, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
  rw [hQd]
  refine le_trans htri ?_
  have hAB : ‖Bd k (cutMul χ f) (cutMul χ f) - Bd k f (cutMul χ f)‖
        + ‖Bd k f (cutMul χ f) - Bd k f f‖
      ≤ (2 * (Df * (Df + m * G)) + G * (m * (Df + m * G))
          + 8 * ((k : ℝ) - 1) ^ 2 * (m * Mf))
          * (volume : Measure ℂ).real (disk ∩ S)
        + (2 * (Df * Df) + G * (m * Df) + 8 * ((k : ℝ) - 1) ^ 2 * (m * Mf))
          * (volume : Measure ℂ).real (disk ∩ S) := by
    rw [hBsym]
    exact add_le_add hA hB
  refine le_trans hAB ?_
  have hmono : (2 * (Df * Df) + G * (m * Df) + 8 * ((k : ℝ) - 1) ^ 2 * (m * Mf))
      ≤ (2 * (Df * (Df + m * G)) + G * (m * (Df + m * G))
          + 8 * ((k : ℝ) - 1) ^ 2 * (m * Mf)) := by
    nlinarith [mul_nonneg hm0 hG0, mul_nonneg (mul_nonneg hm0 hG0) hDf0,
      mul_nonneg hG0 (mul_nonneg hm0 (mul_nonneg hm0 hG0))]
  nlinarith [mul_le_mul_of_nonneg_right hmono hvol0]

end KsIndex.CollarBound
