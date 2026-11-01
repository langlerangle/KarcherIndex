module

/-
# Gradient and energy of a single disk mode

The explicit mode is `modeU k ℓ w = ↑(gRad k ℓ ‖w‖) * w^ℓ`.
Its squared modulus equals `(uRad k ℓ ‖w‖)^2`. For `k ≥ 2`, `ℓ ≥ 1`
and `w ≠ 0`, `gradSq_modeU` identifies its flat gradient density with
`(uD2 k ℓ ‖w‖)^2 + ℓ² * (uRad k ℓ ‖w‖)^2 / ‖w‖²`.

The disk energy is `2π * ℓ² * σ_k(ℓ)`, since the boundary amplitude is `ℓ`.
The value `2π * σ_k(ℓ)` instead belongs to the trace-normalized profile
`phiExt = uRad / ℓ`. Both flat densities are proved integrable on the disk,
and conformal rescaling gives the same energy for `dirichletG - potentialG`.

The gradient calculation differentiates the polynomial angular factor and
the radial factor away from the origin, then evaluates their real Fréchet
derivatives on the basis `{1, I}`. A continuous radial surrogate supplies
the integrability argument across the origin.
-/
public import KsIndexLean.JacobiExtension

@[expose] public section


noncomputable section

namespace KsIndex.JacobiMode

open Complex Real KsIndex.Radial KsIndex.JacobiExtension KsIndex.Surface
open scoped RealInnerProductSpace

variable {k ℓ : ℕ}

/-- The ℓ-th disk mode with radial profile `gRad`: `modeU k ℓ w = g_{k,ℓ}(‖w‖) · w^ℓ`. -/
def modeU (k ℓ : ℕ) (w : ℂ) : ℂ := (gRad k ℓ ‖w‖ : ℂ) * w ^ ℓ

/-! ### Elementary complex-norm computations -/

/-- `‖z‖² = z.re² + z.im²`. -/
lemma nsq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring

/-- `‖P + q·w‖²` for real `P, q`. -/
lemma norm_sq_ofReal_add (P q : ℝ) (w : ℂ) :
    ‖(P : ℂ) + (q : ℂ) * w‖ ^ 2 = P ^ 2 + q ^ 2 * ‖w‖ ^ 2 + 2 * P * q * w.re := by
  rw [nsq, nsq]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, zero_add]
  ring

/-- `‖P·I + q·w‖²` for real `P, q`. -/
lemma norm_sq_ofReal_I_add (P q : ℝ) (w : ℂ) :
    ‖(P : ℂ) * I + (q : ℂ) * w‖ ^ 2 = P ^ 2 + q ^ 2 * ‖w‖ ^ 2 + 2 * P * q * w.im := by
  rw [nsq, nsq]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, sub_zero, add_zero, zero_add, mul_one, zero_sub, neg_neg]
  ring

/-! ### The derivative of the norm off the origin -/

/-- `‖·‖ : ℂ → ℝ` is Fréchet-differentiable away from `0`, with derivative `(‖w‖)⁻¹ • innerSL ℝ w`. -/
lemma hasFDerivAt_norm_ne {w : ℂ} (hw : w ≠ 0) :
    HasFDerivAt (fun z : ℂ => ‖z‖) ((‖w‖)⁻¹ • innerSL ℝ w) w := by
  have hpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hns : HasFDerivAt (fun z : ℂ => ‖z‖ ^ 2) (2 • innerSL ℝ w) w :=
    (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (‖w‖ ^ 2))) (‖w‖ ^ 2) :=
    Real.hasDerivAt_sqrt (by positivity)
  have hwne : ‖w‖ ≠ 0 := hpos.ne'
  have h : HasFDerivAt (fun z : ℂ => ‖z‖)
      ((1 / (2 * Real.sqrt (‖w‖ ^ 2))) • (2 • innerSL ℝ w)) w := by
    refine (hsqrt.comp_hasFDerivAt w hns).congr_of_eventuallyEq ?_
    filter_upwards with z
    exact (Real.sqrt_sq (norm_nonneg z)).symm
  have hderiv : (1 / (2 * Real.sqrt (‖w‖ ^ 2))) • (2 • innerSL ℝ w) = (‖w‖)⁻¹ • innerSL ℝ w := by
    ext y
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul,
      Real.sqrt_sq (norm_nonneg w)]
    field_simp
    ring
  rwa [hderiv] at h

/-! ### Evaluating the inner product on the real basis of `ℂ` -/

lemma innerSL_one (w : ℂ) : innerSL ℝ w (1 : ℂ) = w.re := by
  rw [innerSL_apply_apply, Complex.inner]
  simp

lemma innerSL_I (w : ℂ) : innerSL ℝ w I = w.im := by
  rw [innerSL_apply_apply, Complex.inner]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
    zero_mul, one_mul, zero_sub, neg_neg, sub_zero]

/-! ### The pointwise polar-gradient identity -/

/-- **The flat gradient of the mode** equals the radial energy density: for `w ≠ 0`,
`|∇(modeU k ℓ)|² = (u')² + ℓ² u²/r²` with `u = uRad`, `u' = uD2`, `r = ‖w‖`. -/
theorem gradSq_modeU (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) {w : ℂ} (hw : w ≠ 0) :
    gradSq (modeU k ℓ) w
      = (uD2 k ℓ ‖w‖) ^ 2 + (ℓ : ℝ) ^ 2 * (uRad k ℓ ‖w‖) ^ 2 / ‖w‖ ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
  have hrpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hr : ‖w‖ ≠ 0 := hrpos.ne'
  -- the three factors and the product rule
  have hB : HasFDerivAt (fun z : ℂ => z ^ (j + 1))
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (((j + 1 : ℕ) : ℂ) * w ^ (j + 1 - 1))).restrictScalars ℝ) w :=
    (hasDerivAt_pow (j + 1) w).hasFDerivAt.restrictScalars ℝ
  have hR : HasFDerivAt (fun z : ℂ => gRad k (j + 1) ‖z‖)
      ((gD k ‖w‖) • ((‖w‖)⁻¹ • innerSL ℝ w)) w :=
    (gRad_hasDerivAt hk (j + 1) ‖w‖).comp_hasFDerivAt w (hasFDerivAt_norm_ne hw)
  have hA : HasFDerivAt (fun z : ℂ => (gRad k (j + 1) ‖z‖ : ℂ))
      (Complex.ofRealCLM.comp ((gD k ‖w‖) • ((‖w‖)⁻¹ • innerSL ℝ w))) w :=
    Complex.ofRealCLM.hasFDerivAt.comp w hR
  have hf : HasFDerivAt (modeU k (j + 1)) _ w := hA.mul hB
  -- the two directional derivatives, factored through `w^j`
  have e1 : fderiv ℝ (modeU k (j + 1)) w (1 : ℂ)
      = w ^ j * ((↑(gRad k (j + 1) ‖w‖ * ((j : ℝ) + 1)) : ℂ)
          + (↑(gD k ‖w‖ * (‖w‖)⁻¹ * w.re) : ℂ) * w) := by
    rw [hf.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
      Complex.ofRealCLM_apply, innerSL_one, smul_eq_mul, Nat.add_sub_cancel]
    push_cast
    ring
  have eI : fderiv ℝ (modeU k (j + 1)) w I
      = w ^ j * ((↑(gRad k (j + 1) ‖w‖ * ((j : ℝ) + 1)) : ℂ) * I
          + (↑(gD k ‖w‖ * (‖w‖)⁻¹ * w.im) : ℂ) * w) := by
    rw [hf.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
      Complex.ofRealCLM_apply, innerSL_I, smul_eq_mul, Nat.add_sub_cancel]
    push_cast
    ring
  have hgrad : gradSq (modeU k (j + 1)) w
      = ‖fderiv ℝ (modeU k (j + 1)) w 1‖ ^ 2 + ‖fderiv ℝ (modeU k (j + 1)) w I‖ ^ 2 := rfl
  -- the θ-independent bracket sum (where a² + b² = r² is used)
  have key : ‖(↑(gRad k (j + 1) ‖w‖ * ((j : ℝ) + 1)) : ℂ)
                + (↑(gD k ‖w‖ * (‖w‖)⁻¹ * w.re) : ℂ) * w‖ ^ 2
             + ‖(↑(gRad k (j + 1) ‖w‖ * ((j : ℝ) + 1)) : ℂ) * I
                + (↑(gD k ‖w‖ * (‖w‖)⁻¹ * w.im) : ℂ) * w‖ ^ 2
           = 2 * (gRad k (j + 1) ‖w‖) ^ 2 * ((j : ℝ) + 1) ^ 2
             + 2 * (gRad k (j + 1) ‖w‖) * ((j : ℝ) + 1) * gD k ‖w‖ * ‖w‖
             + (gD k ‖w‖) ^ 2 * ‖w‖ ^ 2 := by
    rw [norm_sq_ofReal_add, norm_sq_ofReal_I_add]
    have hns : w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := (nsq w).symm
    field_simp
    linear_combination (‖w‖ * gD k ‖w‖ ^ 2
        + 2 * gRad k (j + 1) ‖w‖ * ((j : ℝ) + 1) * gD k ‖w‖) * hns
  rw [hgrad, e1, eI]
  simp only [norm_mul, mul_pow, norm_pow]
  rw [← mul_add, key]
  -- pure ‖w‖-arithmetic (no w.re/w.im), unfold uD2, uRad
  simp only [uD2, uRad, Nat.add_sub_cancel, pow_succ]
  push_cast
  field_simp
  ring

/-! ### The one-disk (half-period) Jacobi energy of the mode -/

open MeasureTheory intervalIntegral Set

/-- The radial Jacobi energy density of the `ℓ`-th mode: `H(r) = (∂_r u)² + ℓ²u²/r² − V u²`
with `u = uRad`, `∂_r u = uD2`.  For `w ≠ 0`, `gradSq(modeU) w − V|modeU|² = Hval ‖w‖`. -/
def Hval (k ℓ : ℕ) (r : ℝ) : ℝ :=
  uD2 k ℓ r ^ 2 + (ℓ : ℝ) ^ 2 * uRad k ℓ r ^ 2 / r ^ 2 - Vrad k r * uRad k ℓ r ^ 2

/-- `‖modeU k ℓ w‖² = (uRad k ℓ ‖w‖)²` (the mode's modulus is the radial profile). -/
lemma modeU_normSq (k ℓ : ℕ) (w : ℂ) :
    ‖modeU k ℓ w‖ ^ 2 = uRad k ℓ ‖w‖ ^ 2 := by
  simp only [modeU, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, mul_pow, sq_abs,
    uRad]
  ring

/-- The flat integrand of the half-period energy is the radial density, off the centre. -/
lemma integrand_eq_Hval (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) {w : ℂ} (hw : w ≠ 0) :
    gradSq (modeU k ℓ) w - potV k w * ‖modeU k ℓ w‖ ^ 2 = Hval k ℓ ‖w‖ := by
  rw [gradSq_modeU hk hℓ hw, modeU_normSq, potV_eq_Vrad, Hval]

/-- `r · Hval = lhs` (the polar Jacobian `r` turns the flat density into the radial one). -/
lemma r_mul_Hval {r : ℝ} (hr : r ≠ 0) :
    r * Hval k ℓ r = lhs k ℓ (uRad k ℓ) (uD2 k ℓ) r := by
  rw [Hval, lhs]; field_simp

/-- The mode's radial energy is `ℓ²` times the normalized profile's (`uRad = ℓ·phiExt`). -/
lemma lhs_uRad_eq (hℓ : 1 ≤ ℓ) (r : ℝ) :
    lhs k ℓ (uRad k ℓ) (uD2 k ℓ) r
      = (ℓ : ℝ) ^ 2 * lhs k ℓ (phiExt k ℓ) (phiExtD k ℓ) r := by
  have hl : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
  simp only [lhs, phiExt, phiExtD]
  field_simp

/-- **The one-disk Jacobi energy of the `ℓ`-th mode.**  The flat half-period energy
`∫_D (|∇(modeU)|² − V|modeU|²)` equals `2π · ℓ² · σ_k(ℓ)` — the DtN symbol, weighted by the
mode's boundary value `uRad(1) = ℓ`.  (For the trace-normalized profile `φ = uRad/ℓ` this is the
clean `2π σ_k(ℓ)`.)  Proved by the radial reduction `integral_fun_norm_addHaar` (polar
coordinates + the `2π` angular integral) on top of `gradSq_modeU` and `phiExt_energy`. -/
theorem modeU_disk_energy (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) :
    ∫ w in disk, (gradSq (modeU k ℓ) w - potV k w * ‖modeU k ℓ w‖ ^ 2)
      = 2 * Real.pi * ((ℓ : ℝ) ^ 2 * sigma k ℓ) := by
  have hmeas : MeasurableSet disk := by rw [disk]; exact measurableSet_ball
  -- the cutoff radial profile, supported on `[0,1)`
  set Fp : ℝ → ℝ := fun r => if r < 1 then Hval k ℓ r else 0 with hFp
  -- volume of the unit disk in `ℂ` is `π`
  have hvol : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    rw [Measure.real, Complex.volume_ball]
    simp [NNReal.coe_real_pi]
  -- Step A: the disk integral equals the global integral of `Fp ∘ ‖·‖`
  have hA : ∫ w in disk, (gradSq (modeU k ℓ) w - potV k w * ‖modeU k ℓ w‖ ^ 2)
      = ∫ w : ℂ, Fp ‖w‖ := by
    have hcongr : ∫ w in disk, (gradSq (modeU k ℓ) w - potV k w * ‖modeU k ℓ w‖ ^ 2)
        = ∫ w in disk, Fp ‖w‖ := by
      refine setIntegral_congr_ae hmeas ?_
      have h0 : ∀ᵐ w : ℂ ∂volume, w ≠ 0 := by
        rw [ae_iff]; simpa using measure_singleton (0 : ℂ)
      filter_upwards [h0] with w hw hwd
      have hlt : ‖w‖ < 1 := by
        rw [disk, Metric.mem_ball, dist_zero_right] at hwd; exact hwd
      rw [integrand_eq_Hval hk hℓ hw, hFp]; simp only [hlt, if_true]
    have hind : (fun w : ℂ => Fp ‖w‖) = disk.indicator (fun w => Fp ‖w‖) := by
      funext w
      by_cases hwd : w ∈ disk
      · rw [Set.indicator_of_mem hwd]
      · rw [Set.indicator_of_notMem hwd]
        have hge : ¬ ‖w‖ < 1 := by
          rw [disk, Metric.mem_ball, dist_zero_right] at hwd; exact hwd
        simp only [hFp, if_neg hge]
    rw [hcongr, ← MeasureTheory.integral_indicator hmeas, ← hind]
  rw [hA, integral_fun_norm_addHaar (μ := (volume : Measure ℂ)) (f := Fp),
    Complex.finrank_real_complex, hvol]
  simp only [Nat.reduceSub, pow_one, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  -- Step C: restrict the radial integral to `(0,1)` and identify the integrand with `lhs`
  have hC : ∫ y in Ioi (0:ℝ), y * Fp y = ∫ y in Ioo (0:ℝ) 1, y * Hval k ℓ y := by
    have hpt : (Ioi (0:ℝ)).indicator (fun y => y * Fp y)
             = (Ioo (0:ℝ) 1).indicator (fun y => y * Hval k ℓ y) := by
      funext y
      simp only [Set.indicator_apply, mem_Ioi, mem_Ioo, hFp]
      by_cases hy0 : 0 < y
      · by_cases hy1 : y < 1 <;> simp [hy0, hy1]
      · simp [hy0]
    calc ∫ y in Ioi (0:ℝ), y * Fp y
        = ∫ y, (Ioi (0:ℝ)).indicator (fun y => y * Fp y) y :=
          (MeasureTheory.integral_indicator measurableSet_Ioi).symm
      _ = ∫ y, (Ioo (0:ℝ) 1).indicator (fun y => y * Hval k ℓ y) y := by rw [hpt]
      _ = ∫ y in Ioo (0:ℝ) 1, y * Hval k ℓ y := MeasureTheory.integral_indicator measurableSet_Ioo
  have hD : ∫ y in Ioo (0:ℝ) 1, y * Hval k ℓ y
          = ∫ y in Ioo (0:ℝ) 1, lhs k ℓ (uRad k ℓ) (uD2 k ℓ) y := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun y hy => ?_)
    exact r_mul_Hval (ne_of_gt hy.1)
  have hE : ∫ y in Ioo (0:ℝ) 1, lhs k ℓ (uRad k ℓ) (uD2 k ℓ) y
          = (ℓ : ℝ) ^ 2 * ∫ y in Ioo (0:ℝ) 1, lhs k ℓ (phiExt k ℓ) (phiExtD k ℓ) y := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo (fun y _ => ?_)
    exact lhs_uRad_eq hℓ y
  have hF : ∫ y in Ioo (0:ℝ) 1, lhs k ℓ (phiExt k ℓ) (phiExtD k ℓ) y = sigma k ℓ := by
    have h01 : ∫ y in Ioo (0:ℝ) 1, lhs k ℓ (phiExt k ℓ) (phiExtD k ℓ) y
             = ∫ y in Ioc (0:ℝ) 1, lhs k ℓ (phiExt k ℓ) (phiExtD k ℓ) y :=
      setIntegral_congr_set (Ioo_ae_eq_Ioc' (by simp))
    rw [h01, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), phiExt_energy hk hℓ]
  rw [hC, hD, hE, hF]; ring

/-! ### Integrability of the two flat densities on the disk

Both densities restrict to (a.e.) continuous functions on the compact closed disk `D̄`, hence are
integrable there and so on `D`.  The potential density `V_k|modeU|²` is continuous outright; the
Dirichlet density `gradSq(modeU)` has a removable `/‖w‖²` singularity at the centre
(`(uRad r)²/r² = r^{2ℓ−2}(gRad r)²` for `ℓ ≥ 1`), so it agrees off `0` with a continuous surrogate. -/

/-- The continuous radial surrogate for `gradSq(modeU)`: the `/‖w‖²` singularity of the Dirichlet
density is removable for `ℓ ≥ 1` because `(uRad r)²/r² = r^{2ℓ−2}(gRad r)²`. -/
def Ddens (k ℓ : ℕ) (w : ℂ) : ℝ :=
  (uD2 k ℓ ‖w‖) ^ 2 + (ℓ : ℝ) ^ 2 * ‖w‖ ^ (2 * ℓ - 2) * (gRad k ℓ ‖w‖) ^ 2

lemma continuous_Ddens (hk : 2 ≤ k) (ℓ : ℕ) : Continuous (Ddens k ℓ) := by
  have h1 : Continuous fun w : ℂ => (uD2 k ℓ ‖w‖) ^ 2 :=
    ((uD2_continuous hk ℓ).comp continuous_norm).pow 2
  have h2 : Continuous fun w : ℂ => ‖w‖ ^ (2 * ℓ - 2) := continuous_norm.pow _
  have h3 : Continuous fun w : ℂ => (gRad k ℓ ‖w‖) ^ 2 :=
    ((gRad_continuous hk ℓ).comp continuous_norm).pow 2
  exact h1.add ((continuous_const.mul h2).mul h3)

/-- Off the centre, the mode's Dirichlet density equals its continuous surrogate. -/
lemma gradSq_modeU_eq_Ddens (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) {w : ℂ} (hw : w ≠ 0) :
    gradSq (modeU k ℓ) w = Ddens k ℓ w := by
  have hrne : ‖w‖ ≠ 0 := (norm_pos_iff.mpr hw).ne'
  rw [gradSq_modeU hk hℓ hw, Ddens, uRad]
  have h1 : (‖w‖ ^ ℓ) ^ 2 = ‖w‖ ^ (2 * ℓ - 2) * ‖w‖ ^ 2 := by
    rw [← pow_add, ← pow_mul]; congr 1; omega
  rw [mul_pow, h1]
  field_simp

/-- **The Dirichlet density is integrable on the disk** — a.e. equal to the continuous surrogate
`Ddens`, which is integrable on the compact closed disk. -/
lemma integrableOn_gradSq_modeU (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) :
    IntegrableOn (gradSq (modeU k ℓ)) disk := by
  have hInt : IntegrableOn (Ddens k ℓ) disk :=
    ((continuous_Ddens hk ℓ).continuousOn.integrableOn_compact
      (ProperSpace.isCompact_closedBall (0 : ℂ) 1)).mono_set
      (by rw [disk]; exact Metric.ball_subset_closedBall)
  have hae : gradSq (modeU k ℓ) =ᵐ[volume.restrict disk] Ddens k ℓ := by
    have h0 : ∀ᵐ w ∂(volume.restrict disk), w ≠ (0 : ℂ) :=
      ae_restrict_of_ae (by rw [ae_iff]; simpa using measure_singleton (0 : ℂ))
    filter_upwards [h0] with w hw using gradSq_modeU_eq_Ddens hk hℓ hw
  exact Integrable.congr hInt hae.symm

/-- **The potential density is integrable on the disk** — it is continuous (`V_k` continuous for
`k ≥ 2`, `‖modeU‖² = (uRad ∘ ‖·‖)²`), hence integrable on the compact closed disk. -/
lemma integrableOn_potMode (hk : 2 ≤ k) (ℓ : ℕ) :
    IntegrableOn (fun w => potV k w * ‖modeU k ℓ w‖ ^ 2) disk := by
  have huRad : Continuous (uRad k ℓ) :=
    continuous_iff_continuousAt.mpr fun r => (uRad_hasDerivAt' hk ℓ r).continuousAt
  have hcont : Continuous fun w : ℂ => potV k w * ‖modeU k ℓ w‖ ^ 2 := by
    have heq : (fun w : ℂ => potV k w * ‖modeU k ℓ w‖ ^ 2)
             = fun w : ℂ => Vrad k ‖w‖ * (uRad k ℓ ‖w‖) ^ 2 := by
      funext w; rw [potV_eq_Vrad, modeU_normSq]
    rw [heq]
    exact ((continuous_Vrad k).comp continuous_norm).mul ((huRad.comp continuous_norm).pow 2)
  exact (hcont.continuousOn.integrableOn_compact
    (ProperSpace.isCompact_closedBall (0 : ℂ) 1)).mono_set
    (by rw [disk]; exact Metric.ball_subset_closedBall)

/-! ### The conformal-collapse corollary: the mode's contribution to `jacobiQ` -/

/-- **Conformal-collapse corollary — the mode's contribution to `Surface.jacobiQ`.**  The geometric
half-period Jacobi form `dirichletG − potentialG` (carrying the metric factor `ρ_k²`), evaluated on
the `ℓ`-th disk mode, equals the DtN symbol value `2π·ℓ²·σ_k(ℓ)` from `modeU_disk_energy`.  The `ρ_k²` has
cancelled on the open disk (`Surface.dirichletG_sub_potentialG`, using that the punctures miss the
disk), the two flat densities are integrable there (`integrableOn_gradSq_modeU`,
`integrableOn_potMode`), so `∫A − ∫B = ∫(A−B) = modeU_disk_energy`. The hypotheses are `k ≥ 2` and `ℓ ≥ 1`. -/
theorem modeU_jacobiQ_summand (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) :
    dirichletG k (modeU k ℓ) - potentialG k (modeU k ℓ)
      = 2 * Real.pi * ((ℓ : ℝ) ^ 2 * sigma k ℓ) := by
  rw [dirichletG_sub_potentialG hk,
    ← MeasureTheory.integral_sub (integrableOn_gradSq_modeU hk hℓ) (integrableOn_potMode hk ℓ)]
  exact modeU_disk_energy hk hℓ
