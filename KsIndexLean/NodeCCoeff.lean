module

public import KsIndexLean.NodeCPairing

@[expose] public section


/-!
# Fourier coefficients of the mixed-boundary trial function

For nonzero integer `m`, the half-circle exponential integral is
`∫_{-π/2}^{π/2} e^{-i m θ} dθ = 2 sin(mπ/2)/m`; at `m = 0` it is `π`.
Splitting a full-period integral into two semicircles gives the trial coefficient
formula with Fourier normalization `(2π)⁻¹`. On the left semicircle, the
piecewise formula is used almost everywhere, excluding the endpoint discrepancy.

The coefficients at `0` and `-1` vanish. For the remaining indices,
`(2+π)/2 · |Ψ̂(ℓ)|` equals `|ℓ+1|⁻¹` for even `ℓ` and `|ℓ|⁻¹` for odd `ℓ`.
The final theorems express these identities as squared norms, with the
exceptional indices explicitly excluded. These coefficients supply the
trial-tail estimate used in the paper's `Q`-lower argument.

-/

noncomputable section
open MeasureTheory Complex
namespace KsIndex.NodeC
open KsIndex.Trace KsIndex.Parseval intervalIntegral

/-- The half-circle exponential integral. -/
lemma arc_exp_integral {m : ℤ} (hm : m ≠ 0) :
    (∫ θ in (-(Real.pi / 2))..(Real.pi / 2), Complex.exp (-(m : ℂ) * Complex.I * θ))
      = ((2 * Real.sin ((m : ℝ) * Real.pi / 2) / (m : ℝ) : ℝ) : ℂ) := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hc : -(m : ℂ) * Complex.I ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hmC) Complex.I_ne_zero
  rw [integral_exp_mul_complex hc]
  have he1 : (-(m : ℂ) * Complex.I) * ((Real.pi / 2 : ℝ) : ℂ)
      = (-(((m : ℝ) * Real.pi / 2 : ℝ) : ℂ)) * Complex.I := by push_cast; ring
  have he2 : (-(m : ℂ) * Complex.I) * ((-(Real.pi / 2) : ℝ) : ℂ)
      = (((m : ℝ) * Real.pi / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he1, he2, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  push_cast [Complex.ofReal_sin]
  field_simp
  ring

/-! ### The `sin(mπ/2)` parity casework -/

/-- `sin(mπ/2) = 0` for even `m`. -/
lemma sin_even_pi_half (t : ℤ) : Real.sin (((2 * t : ℤ) : ℝ) * Real.pi / 2) = 0 := by
  have harg : ((2 * t : ℤ) : ℝ) * Real.pi / 2 = (t : ℝ) * Real.pi := by push_cast; ring
  rw [harg, Real.sin_int_mul_pi]

/-- `cos(mπ/2) = 0` for odd `m`. -/
lemma cos_odd_pi_half (t : ℤ) : Real.cos (((2 * t + 1 : ℤ) : ℝ) * Real.pi / 2) = 0 := by
  have harg : ((2 * t + 1 : ℤ) : ℝ) * Real.pi / 2 = (t : ℝ) * Real.pi + Real.pi / 2 := by
    push_cast; ring
  rw [harg, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.sin_int_mul_pi]
  ring

/-- `sin²(mπ/2) = 1` for odd `m` — hence `|sin(mπ/2)| = 1`. -/
lemma sin_sq_odd_pi_half (t : ℤ) : (Real.sin (((2 * t + 1 : ℤ) : ℝ) * Real.pi / 2)) ^ 2 = 1 := by
  have h := Real.sin_sq_add_cos_sq (((2 * t + 1 : ℤ) : ℝ) * Real.pi / 2)
  rw [cos_odd_pi_half] at h
  nlinarith [h]

/-! ### Exponential modes and interval integrability -/

/-- The pure exponential mode `e^{−imθ}` (the `fc` integrand kernel). -/
def Emode (m : ℤ) (θ : ℝ) : ℂ := Complex.exp (-(m : ℂ) * Complex.I * θ)

lemma continuous_Emode (m : ℤ) : Continuous (Emode m) := by
  unfold Emode
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

/-- Each mode has unit modulus (its exponent is purely imaginary). -/
lemma norm_Emode (m : ℤ) (θ : ℝ) : ‖Emode m θ‖ = 1 := by
  unfold Emode
  rw [show -(m : ℂ) * Complex.I * (θ : ℂ) = ((-(m : ℝ) * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- Modes are `2π`-periodic (integer frequency). -/
lemma Emode_periodic (m : ℤ) : Function.Periodic (Emode m) (2 * Real.pi) := by
  intro θ
  unfold Emode
  rw [show -(m : ℂ) * Complex.I * ((θ + 2 * Real.pi : ℝ) : ℂ)
      = -(m : ℂ) * Complex.I * (θ : ℂ) + ((-m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The half-circle integral of a mode. -/
def arcInt (m : ℤ) : ℂ := ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), Emode m θ

lemma arcInt_ne_zero {m : ℤ} (hm : m ≠ 0) :
    arcInt m = ((2 * Real.sin ((m : ℝ) * Real.pi / 2) / (m : ℝ) : ℝ) : ℂ) := by
  unfold arcInt Emode
  exact arc_exp_integral hm

lemma arcInt_zero : arcInt 0 = (Real.pi : ℂ) := by
  unfold arcInt Emode
  simp only [Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const]
  rw [Complex.real_smul, mul_one]
  push_cast; ring

/-- `(cP θ).re = cos θ`. -/
lemma circleParam_re (θ : ℝ) : ((circleParam θ : ℂ)).re = Real.cos θ := by
  rw [circleParam_coe, Complex.exp_ofReal_mul_I_re]

/-- The un-damped integrand `(1 − conj w)·e^{−iℓθ}` splits into two modes. -/
lemma one_sub_conj_mul_Emode (ℓ : ℤ) (θ : ℝ) :
    (1 - (starRingEnd ℂ) (circleParam θ : ℂ)) * Emode ℓ θ = Emode ℓ θ - Emode (ℓ + 1) θ := by
  have hconj : (starRingEnd ℂ) (circleParam θ : ℂ) * Emode ℓ θ = Emode (ℓ + 1) θ := by
    rw [conj_circleParam]
    unfold Emode
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  rw [sub_mul, one_mul, hconj]

/-- On the cap `cos θ ≥ 0` the damping factor is `1`. -/
lemma psiIntegrand_eq_of_re_nonneg {ℓ : ℤ} {θ : ℝ} (h : 0 ≤ ((circleParam θ : ℂ)).re) :
    trialPsi (circleParam θ) * Emode ℓ θ = Emode ℓ θ - Emode (ℓ + 1) θ := by
  rw [trialPsi_of_re_nonneg h, one_sub_conj_mul_Emode]

/-- On the middle `cos θ < 0` the damping factor is `psiFactor`. -/
lemma psiIntegrand_eq_of_re_neg {ℓ : ℤ} {θ : ℝ} (h : ((circleParam θ : ℂ)).re < 0) :
    trialPsi (circleParam θ) * Emode ℓ θ = (psiFactor : ℂ) * (Emode ℓ θ - Emode (ℓ + 1) θ) := by
  unfold trialPsi
  rw [if_neg (not_le.mpr h),
    show (1 - (starRingEnd ℂ) (circleParam θ : ℂ)) * (psiFactor : ℂ) * Emode ℓ θ
      = (psiFactor : ℂ) * ((1 - (starRingEnd ℂ) (circleParam θ : ℂ)) * Emode ℓ θ) by ring,
    one_sub_conj_mul_Emode]

/-- The damped `fc` integrand is bounded and measurable, hence interval-integrable. -/
lemma psiIntegrand_intervalIntegrable (ℓ : ℤ) (a b : ℝ) :
    IntervalIntegrable (fun θ => trialPsi (circleParam θ) * Emode ℓ θ) volume a b := by
  have hmeas : Measurable (fun θ => trialPsi (circleParam θ) * Emode ℓ θ) :=
    (measurable_trialPsi.comp measurable_circleParam).mul (continuous_Emode ℓ).measurable
  have hbound : ∀ θ, ‖trialPsi (circleParam θ) * Emode ℓ θ‖ ≤ 2 := by
    intro θ
    rw [norm_mul, norm_Emode, mul_one]
    exact norm_trialPsi_le _
  refine ⟨?_, ?_⟩ <;>
    exact IntegrableOn.of_bound measure_Ioc_lt_top hmeas.aestronglyMeasurable.restrict 2
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun θ _ => hbound θ))

/-- Definitional unfolding of a mode (for folding `exp` back to `Emode`). -/
lemma Emode_apply (m : ℤ) (θ : ℝ) : Emode m θ = Complex.exp (-(m : ℂ) * Complex.I * θ) := rfl

/-- `fc` written with the mode kernel and the coercion in `(↑·)⁻¹` normal form. -/
lemma fc_eq_Emode_integral (g : ℝ → ℂ) (ℓ : ℤ) :
    fc g ℓ = ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, g θ * Emode ℓ θ := by
  rw [Parseval.fc, Complex.ofReal_inv]
  rfl

/-! ### Window reduction and coefficient formula -/

/-- **The window reduction.**  The full-period integral of the damped `fc` integrand,
computed by shifting to `[−π/2, 3π/2]`, splitting at `π/2`, and identifying `Ψ∘cP` with
`1 − conj w` on the `cos ≥ 0` cap and `psiFactor·(1 − conj w)` a.e. on the `cos ≤ 0` middle. -/
lemma trialPsi_integral_value (ℓ : ℤ) :
    (∫ θ in (0:ℝ)..2 * Real.pi, trialPsi (circleParam θ) * Emode ℓ θ)
      = (1 - (psiFactor : ℂ)) * (arcInt ℓ - arcInt (ℓ + 1))
        + (psiFactor : ℂ) * (((2 * Real.pi : ℝ) : ℂ)
            * ((if ℓ = 0 then 1 else 0) - (if ℓ = -1 then 1 else 0))) := by
  have hπ := Real.pi_pos
  -- periodicity of the two integrands
  have hFper : Function.Periodic (fun θ => trialPsi (circleParam θ) * Emode ℓ θ) (2 * Real.pi) :=
    fun θ => by simp only [circleParam_periodic θ, Emode_periodic ℓ θ]
  have hBper : Function.Periodic (fun θ => Emode ℓ θ - Emode (ℓ + 1) θ) (2 * Real.pi) :=
    fun θ => by simp only [Emode_periodic ℓ θ, Emode_periodic (ℓ + 1) θ]
  have hBc : Continuous (fun θ => Emode ℓ θ - Emode (ℓ + 1) θ) :=
    (continuous_Emode ℓ).sub (continuous_Emode (ℓ + 1))
  -- shift the `Ψ` integral to the symmetric window
  have hshiftF : (∫ θ in (0:ℝ)..2 * Real.pi, trialPsi (circleParam θ) * Emode ℓ θ)
      = ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2), trialPsi (circleParam θ) * Emode ℓ θ := by
    have h := hFper.intervalIntegral_add_eq 0 (-(Real.pi / 2))
    rw [zero_add, show -(Real.pi / 2) + 2 * Real.pi = 3 * Real.pi / 2 by ring] at h
    exact h
  have hsplitF : (∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2), trialPsi (circleParam θ) * Emode ℓ θ)
      = (∫ θ in (-(Real.pi / 2))..(Real.pi / 2), trialPsi (circleParam θ) * Emode ℓ θ)
        + ∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), trialPsi (circleParam θ) * Emode ℓ θ :=
    (integral_add_adjacent_intervals (psiIntegrand_intervalIntegrable ℓ _ _)
      (psiIntegrand_intervalIntegrable ℓ _ _)).symm
  -- cap: `Ψ∘cP = 1 − conj w`
  have hcapF : (∫ θ in (-(Real.pi / 2))..(Real.pi / 2), trialPsi (circleParam θ) * Emode ℓ θ)
      = ∫ θ in (-(Real.pi / 2))..(Real.pi / 2), (Emode ℓ θ - Emode (ℓ + 1) θ) := by
    refine intervalIntegral.integral_congr (fun θ hθ => ?_)
    rw [Set.uIcc_of_le (by linarith : -(Real.pi / 2) ≤ Real.pi / 2)] at hθ
    have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc hθ
    rw [← circleParam_re θ] at hcos
    exact psiIntegrand_eq_of_re_nonneg hcos
  have hcapVal : (∫ θ in (-(Real.pi / 2))..(Real.pi / 2), (Emode ℓ θ - Emode (ℓ + 1) θ))
      = arcInt ℓ - arcInt (ℓ + 1) := by
    rw [intervalIntegral.integral_sub ((continuous_Emode ℓ).intervalIntegrable _ _)
      ((continuous_Emode (ℓ + 1)).intervalIntegrable _ _)]
    rfl
  -- middle: `Ψ∘cP = psiFactor·(1 − conj w)` a.e.
  have hbad : {θ : ℝ | ¬ (θ ∈ Set.uIoc (Real.pi / 2) (3 * Real.pi / 2) →
      trialPsi (circleParam θ) * Emode ℓ θ
        = (psiFactor : ℂ) * (Emode ℓ θ - Emode (ℓ + 1) θ))} ⊆ {3 * Real.pi / 2} := by
    intro θ hθ
    obtain ⟨hmem, hne⟩ := not_imp.mp hθ
    rw [Set.uIoc_of_le (by linarith : Real.pi / 2 ≤ 3 * Real.pi / 2)] at hmem
    rw [Set.mem_singleton_iff]
    by_contra hne2
    apply hne
    have hθlt : θ < 3 * Real.pi / 2 := lt_of_le_of_ne hmem.2 hne2
    have hmem2 : θ - Real.pi ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [hmem.1], by linarith [hθlt]⟩
    have hcp := Real.cos_pos_of_mem_Ioo hmem2
    have hcc : Real.cos θ = -Real.cos (θ - Real.pi) := by
      rw [Real.cos_sub, Real.cos_pi, Real.sin_pi]; ring
    have hcosneg : Real.cos θ < 0 := by rw [hcc]; linarith
    rw [← circleParam_re θ] at hcosneg
    exact psiIntegrand_eq_of_re_neg hcosneg
  have hae : ∀ᵐ θ ∂volume, θ ∈ Set.uIoc (Real.pi / 2) (3 * Real.pi / 2) →
      trialPsi (circleParam θ) * Emode ℓ θ
        = (psiFactor : ℂ) * (Emode ℓ θ - Emode (ℓ + 1) θ) := by
    rw [MeasureTheory.ae_iff]
    exact measure_mono_null hbad Real.volume_singleton
  have hmidF : (∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), trialPsi (circleParam θ) * Emode ℓ θ)
      = (psiFactor : ℂ)
        * ∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), (Emode ℓ θ - Emode (ℓ + 1) θ) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr_ae hae
  -- the base function over the full period equals `2π·(δ₀ − δ₋₁)`
  have hbaseval : (∫ θ in (0:ℝ)..2 * Real.pi, (Emode ℓ θ - Emode (ℓ + 1) θ))
      = ((2 * Real.pi : ℝ) : ℂ) * ((if ℓ = 0 then 1 else 0) - (if ℓ = -1 then 1 else 0)) := by
    have hne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by rw [Ne, Complex.ofReal_eq_zero]; positivity
    have h2a : fc (fun θ => 1 - (starRingEnd ℂ) (circleParam θ : ℂ)) ℓ
        = (if ℓ = 0 then (1:ℂ) else 0) - (if ℓ = -1 then 1 else 0) := by
      have hcf := circleFourierCoeff_one_sub_conj ℓ
      rwa [circleFourierCoeff_eq_fc] at hcf
    rw [fc_eq_Emode_integral,
      intervalIntegral.integral_congr (g := fun θ => Emode ℓ θ - Emode (ℓ + 1) θ)
        (fun θ _ => one_sub_conj_mul_Emode ℓ θ)] at h2a
    rw [← h2a, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  have hsplitB : (∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2), (Emode ℓ θ - Emode (ℓ + 1) θ))
      = (∫ θ in (-(Real.pi / 2))..(Real.pi / 2), (Emode ℓ θ - Emode (ℓ + 1) θ))
        + ∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), (Emode ℓ θ - Emode (ℓ + 1) θ) :=
    (integral_add_adjacent_intervals (hBc.intervalIntegrable _ _) (hBc.intervalIntegrable _ _)).symm
  have hshiftB : (∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2), (Emode ℓ θ - Emode (ℓ + 1) θ))
      = ∫ θ in (0:ℝ)..2 * Real.pi, (Emode ℓ θ - Emode (ℓ + 1) θ) := by
    have h := hBper.intervalIntegral_add_eq (-(Real.pi / 2)) 0
    rw [zero_add, show -(Real.pi / 2) + 2 * Real.pi = 3 * Real.pi / 2 by ring] at h
    exact h
  have hmidval : (∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), (Emode ℓ θ - Emode (ℓ + 1) θ))
      = ((2 * Real.pi : ℝ) : ℂ) * ((if ℓ = 0 then 1 else 0) - (if ℓ = -1 then 1 else 0))
        - (arcInt ℓ - arcInt (ℓ + 1)) := by
    have h := hsplitB
    rw [hcapVal, hshiftB, hbaseval] at h
    linear_combination -h
  rw [hshiftF, hsplitF, hcapF, hcapVal, hmidF, hmidval]
  ring

/-- **The coefficient formula.**  `Ψ̂(ℓ) = psiFactor·(δ₀ − δ₋₁)
+ (2π)⁻¹(1 − psiFactor)·(arcInt ℓ − arcInt(ℓ+1))`. -/
lemma trialPsi_circleFourierCoeff (ℓ : ℤ) :
    circleFourierCoeff trialPsi ℓ
      = (psiFactor : ℂ) * ((if ℓ = 0 then 1 else 0) - (if ℓ = -1 then 1 else 0))
        + ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (1 - (psiFactor : ℂ)) * (arcInt ℓ - arcInt (ℓ + 1)) := by
  rw [circleFourierCoeff_eq_fc, fc_eq_Emode_integral, trialPsi_integral_value ℓ]
  have hne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by rw [Ne, Complex.ofReal_eq_zero]; positivity
  field_simp
  ring

/-! ### Coefficient values and the squared-norm formula -/

lemma arcInt_one : arcInt 1 = 2 := by
  rw [arcInt_ne_zero (by norm_num : (1:ℤ) ≠ 0),
    show ((1:ℤ):ℝ) * Real.pi / 2 = Real.pi / 2 by push_cast; ring, Real.sin_pi_div_two]
  norm_num

lemma arcInt_neg_one : arcInt (-1) = 2 := by
  rw [arcInt_ne_zero (by norm_num : (-1:ℤ) ≠ 0),
    show ((-1:ℤ):ℝ) * Real.pi / 2 = -(Real.pi / 2) by push_cast; ring, Real.sin_neg,
    Real.sin_pi_div_two]
  norm_num

/-- Nonzero even modes contribute nothing to the arc integral (`sin(tπ) = 0`). -/
lemma arcInt_even {t : ℤ} (ht : t ≠ 0) : arcInt (2 * t) = 0 := by
  rw [arcInt_ne_zero (by omega : (2 * t : ℤ) ≠ 0), sin_even_pi_half t]
  simp

/-- `‖arcInt(2t+1)‖² = 4/(2t+1)²` (odd modes, via `sin² = 1`). -/
lemma normSq_arcInt_odd (t : ℤ) :
    ‖arcInt (2 * t + 1)‖ ^ 2 = 4 / ((2 * t + 1 : ℤ) : ℝ) ^ 2 := by
  rw [arcInt_ne_zero (by omega : (2 * t + 1 : ℤ) ≠ 0), Complex.norm_real, Real.norm_eq_abs,
    sq_abs, div_pow, mul_pow, sin_sq_odd_pi_half t]
  norm_num

/-- The real constant `(2+π)⁻¹` as the modulus of the coefficient prefactor. -/
lemma norm_inv_two_add_pi : ‖((2 + Real.pi : ℝ) : ℂ)⁻¹‖ = (2 + Real.pi)⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- The prefactor identity `(2π)⁻¹(1 − psiFactor) = (2+π)⁻¹`. -/
lemma const_identity : (2 * Real.pi)⁻¹ * (1 - psiFactor) = (2 + Real.pi)⁻¹ := by
  unfold psiFactor
  have hsum : (2 + Real.pi) ≠ 0 := by positivity
  have h2π : (2 * Real.pi) ≠ 0 := by positivity
  field_simp
  ring

/-- **Reduced coefficient** for `ℓ ∉ {0, −1}` — the `δ` terms drop and the prefactor
collapses to `(2+π)⁻¹`. -/
lemma trialPsi_coeff_of_ne {ℓ : ℤ} (h0 : ℓ ≠ 0) (h1 : ℓ ≠ -1) :
    circleFourierCoeff trialPsi ℓ = ((2 + Real.pi : ℝ) : ℂ)⁻¹ * (arcInt ℓ - arcInt (ℓ + 1)) := by
  rw [trialPsi_circleFourierCoeff, if_neg h0, if_neg h1]
  have hc : ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (1 - (psiFactor : ℂ)) = ((2 + Real.pi : ℝ) : ℂ)⁻¹ := by
    exact_mod_cast const_identity
  simp only [sub_zero, mul_zero, zero_add]
  rw [hc]

/-- `Ψ̂(0) = 0` (the `(2−π)/(2+π)` factor kills the constant mode). -/
lemma trialPsi_coeff_zero : circleFourierCoeff trialPsi 0 = 0 := by
  rw [trialPsi_circleFourierCoeff, if_pos rfl, if_neg (by decide : ¬ (0:ℤ) = -1),
    show (0:ℤ) + 1 = 1 by norm_num, arcInt_zero, arcInt_one]
  have hsumC : (2 + (Real.pi : ℂ)) ≠ 0 := by
    rw [show (2 + (Real.pi : ℂ)) = ((2 + Real.pi : ℝ) : ℂ) by push_cast; ring, Ne,
      Complex.ofReal_eq_zero]; positivity
  have h2πC : (2 * (Real.pi : ℂ)) ≠ 0 := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Ne,
      Complex.ofReal_eq_zero]; positivity
  unfold psiFactor
  push_cast
  field_simp
  ring

/-- `Ψ̂(−1) = 0`. -/
lemma trialPsi_coeff_neg_one : circleFourierCoeff trialPsi (-1) = 0 := by
  rw [trialPsi_circleFourierCoeff, if_neg (by decide : ¬ (-1:ℤ) = 0), if_pos rfl,
    show (-1:ℤ) + 1 = 0 by norm_num, arcInt_neg_one, arcInt_zero]
  have hsumC : (2 + (Real.pi : ℂ)) ≠ 0 := by
    rw [show (2 + (Real.pi : ℂ)) = ((2 + Real.pi : ℝ) : ℂ) by push_cast; ring, Ne,
      Complex.ofReal_eq_zero]; positivity
  have h2πC : (2 * (Real.pi : ℂ)) ≠ 0 := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Ne,
      Complex.ofReal_eq_zero]; positivity
  unfold psiFactor
  push_cast
  field_simp
  ring

/-- **`|Ψ̂|²`, even modes** `ℓ = 2t (t ≠ 0)`: `‖Ψ̂(2t)‖² = 4/((2+π)²(2t+1)²)`. -/
lemma trialPsi_normSq_even {t : ℤ} (ht : t ≠ 0) :
    ‖circleFourierCoeff trialPsi (2 * t)‖ ^ 2
      = 4 / ((2 + Real.pi) ^ 2 * ((2 * t + 1 : ℤ) : ℝ) ^ 2) := by
  have h0 : (2 * t : ℤ) ≠ 0 := by omega
  have h1 : (2 * t : ℤ) ≠ -1 := by omega
  have hC : arcInt (2 * t) - arcInt (2 * t + 1) = -arcInt (2 * t + 1) := by
    rw [arcInt_even ht, zero_sub]
  rw [trialPsi_coeff_of_ne h0 h1, hC, norm_mul, mul_pow, norm_inv_two_add_pi, norm_neg,
    normSq_arcInt_odd, inv_pow]
  have hp : (2 + Real.pi) ≠ 0 := by positivity
  have ht0 : ((2 * t + 1 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : (2 * t + 1 : ℤ) ≠ 0)
  field_simp

/-- **`|Ψ̂|²`, odd modes** `ℓ = 2t+1 (t ≠ −1)`: `‖Ψ̂(2t+1)‖² = 4/((2+π)²(2t+1)²)`. -/
lemma trialPsi_normSq_odd {t : ℤ} (ht : t ≠ -1) :
    ‖circleFourierCoeff trialPsi (2 * t + 1)‖ ^ 2
      = 4 / ((2 + Real.pi) ^ 2 * ((2 * t + 1 : ℤ) : ℝ) ^ 2) := by
  have h0 : (2 * t + 1 : ℤ) ≠ 0 := by omega
  have h1 : (2 * t + 1 : ℤ) ≠ -1 := by omega
  have hC : arcInt (2 * t + 1) - arcInt (2 * t + 1 + 1) = arcInt (2 * t + 1) := by
    rw [show (2 * t + 1 + 1 : ℤ) = 2 * (t + 1) by ring, arcInt_even (by omega : (t + 1 : ℤ) ≠ 0),
      sub_zero]
  rw [trialPsi_coeff_of_ne h0 h1, hC, norm_mul, mul_pow, norm_inv_two_add_pi, normSq_arcInt_odd,
    inv_pow]
  have hp : (2 + Real.pi) ≠ 0 := by positivity
  have ht0 : ((2 * t + 1 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast h0
  field_simp

end KsIndex.NodeC
