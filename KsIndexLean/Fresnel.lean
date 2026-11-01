module

/-
# Oscillatory integral estimates for a quadratic phase

For `R > 0` and real `ℓ ≥ 1`, `fresnel_core` bounds the integral of
`A(t) exp(iℓt²)` by `8 (M₀ + M₁ R) / √ℓ`. The amplitude has derivative `A'`
at every point of `[0, R]`, with `A'` continuous there, and the norms of
`A` and `A'` are bounded by `M₀` and `M₁` on that interval.

The proof splits at `t₀ = ℓ^{-1/2}` when `t₀ < R`; otherwise a direct norm
bound suffices. On the remaining interval, integration by parts produces
boundary terms and integrals of `1/t` and `1/t²`. The inequality
`log x ≤ x - 1` gives the required bound without a stationary-phase theorem.

For an amplitude `t² C(t)` with two continuous derivatives and `C(R) = 0`,
`fresnel_peel` first integrates by parts with vanishing boundary terms. Applying
`fresnel_core` to `C(t) + t C'(t)` gives
`4 (N₀ + 3 N₁ R + N₂ R²) ℓ^{-3/2}`, where the `Nᵢ` bound the respective
amplitude derivatives. Finally, `fresnel_cov` proves the substitution `x = t²`
for an arbitrary continuous complex-valued integrand on a positive interval.
-/
public import Mathlib

@[expose] public section


noncomputable section

open MeasureTheory intervalIntegral

namespace KsIndex.Fresnel

/-! ### The phase -/

/-- The quadratic phase has unit modulus. -/
lemma norm_phase (ℓ t : ℝ) : ‖Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)‖ = 1 := by
  have h2 : Complex.I * ℓ * (t : ℂ) ^ 2 = Complex.I * ((ℓ * t ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h2, Complex.norm_exp]
  have h3 : (Complex.I * ((ℓ * t ^ 2 : ℝ) : ℂ)).re = 0 := by
    rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h3, Real.exp_zero]

/-- Derivative of the quadratic phase: `d/dt exp(iℓt²) = (2iℓt)·exp(iℓt²)`. -/
lemma hasDerivAt_phase (ℓ t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * ℓ * (s : ℂ) ^ 2))
      (2 * Complex.I * ℓ * t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (ℓ * s ^ 2 : ℝ)) (ℓ * (2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_mul ℓ
  have h3 : HasDerivAt (fun s : ℝ => Complex.I * ((ℓ * s ^ 2 : ℝ) : ℂ))
      (Complex.I * ((ℓ * (2 * t) : ℝ) : ℂ)) t := h1.ofReal_comp.const_mul Complex.I
  have h4 := h3.cexp
  have hfun : (fun s : ℝ => Complex.exp (Complex.I * ((ℓ * s ^ 2 : ℝ) : ℂ)))
      = fun s : ℝ => Complex.exp (Complex.I * ℓ * (s : ℂ) ^ 2) := by
    funext s; congr 1; push_cast; ring
  have harg : Complex.I * ((ℓ * t ^ 2 : ℝ) : ℂ) = Complex.I * ℓ * (t : ℂ) ^ 2 := by
    push_cast; ring
  rw [hfun, harg] at h4
  convert h4 using 1
  push_cast; ring

/-- Derivative of `t ↦ (c t)⁻¹` off the origin: `−(c t²)⁻¹`. -/
lemma hasDerivAt_invLin {c : ℂ} (hc : c ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => (c * (s : ℂ))⁻¹) (-(c * (t : ℂ) ^ 2)⁻¹) t := by
  have h1 : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c t := by
    simpa using ((hasDerivAt_id t).ofReal_comp.const_mul c)
  have hne : c * (t : ℂ) ≠ 0 := mul_ne_zero hc (by exact_mod_cast ht)
  have h2 : HasDerivAt (fun z : ℂ => z⁻¹) (-((c * (t : ℂ)) ^ 2)⁻¹) (c * (t : ℂ)) :=
    hasDerivAt_inv hne
  have h3 := h2.comp t h1
  have hfun : ((fun z : ℂ => z⁻¹) ∘ fun s : ℝ => c * (s : ℂ))
      = fun s : ℝ => (c * (s : ℂ))⁻¹ := rfl
  rw [hfun] at h3
  have hderiv : -((c * (t : ℂ)) ^ 2)⁻¹ * c = -(c * (t : ℂ) ^ 2)⁻¹ := by
    rw [neg_mul, neg_inj, mul_pow, mul_inv, mul_inv, sq, mul_inv, mul_right_comm,
      mul_assoc c⁻¹ c⁻¹ c, inv_mul_cancel₀ hc, mul_one]
  rw [hderiv] at h3
  exact h3

/-! ### The main estimate -/

/-- **Quadratic-phase integral bound.** For `A` with a continuous derivative `A'` on `[0, R]`,
`‖A‖ ≤ M₀`, `‖A'‖ ≤ M₁` there, and `ℓ ≥ 1`:
`‖∫₀^R A(t)·exp(iℓt²) dt‖ ≤ 8(M₀ + M₁R)·ℓ^{−1/2}`. -/
theorem fresnel_core {A A' : ℝ → ℂ} {R M₀ M₁ ℓ : ℝ} (hR : 0 < R)
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) R, HasDerivAt A (A' t) t)
    (hA'c : ContinuousOn A' (Set.Icc 0 R))
    (hM₀ : ∀ t ∈ Set.Icc (0 : ℝ) R, ‖A t‖ ≤ M₀)
    (hM₁ : ∀ t ∈ Set.Icc (0 : ℝ) R, ‖A' t‖ ≤ M₁)
    (hℓ : 1 ≤ ℓ) :
    ‖∫ t in (0 : ℝ)..R, A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)‖
      ≤ 8 * (M₀ + M₁ * R) * (Real.sqrt ℓ)⁻¹ := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ0
  have hsq : Real.sqrt ℓ * Real.sqrt ℓ = ℓ := Real.mul_self_sqrt hℓ0.le
  set t₀ : ℝ := (Real.sqrt ℓ)⁻¹ with ht₀_def
  have ht₀ : 0 < t₀ := inv_pos.mpr hs
  have ht₀inv : t₀⁻¹ = Real.sqrt ℓ := by rw [ht₀_def, inv_inv]
  have hℓt₀ : ℓ * t₀ = Real.sqrt ℓ := by
    rw [ht₀_def]
    field_simp
    nlinarith [hsq]
  have hkey : (2 * ℓ)⁻¹ * Real.sqrt ℓ = t₀ / 2 := by
    rw [ht₀_def]
    field_simp
    nlinarith [hsq]
  have hM₀0 : 0 ≤ M₀ := le_trans (norm_nonneg _) (hM₀ 0 ⟨le_refl 0, hR.le⟩)
  have hM₁0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0 ⟨le_refl 0, hR.le⟩)
  -- continuity of the integrand on [0, R]
  have hAc : ContinuousOn A (Set.Icc 0 R) := fun t ht =>
    (hA t ht).continuousAt.continuousWithinAt
  have hphase_c : Continuous fun t : ℝ => Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2) := by
    fun_prop
  have hIc : ContinuousOn (fun t : ℝ => A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2))
      (Set.Icc 0 R) := hAc.mul hphase_c.continuousOn
  -- the pointwise bound M₀ on the integrand
  have hIbnd : ∀ t ∈ Set.Icc (0 : ℝ) R,
      ‖A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)‖ ≤ M₀ := by
    intro t ht
    rw [norm_mul, norm_phase, mul_one]
    exact hM₀ t ht
  by_cases hcase : R ≤ t₀
  · -- degenerate case: the whole interval is "head"
    have hbig : ‖∫ t in (0 : ℝ)..R, A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)‖
        ≤ M₀ * |R - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le hR.le] at hx
      exact hIbnd x ⟨hx.1.le, hx.2⟩
    have h1 : M₀ * |R - 0| ≤ M₀ * t₀ := by
      rw [sub_zero, abs_of_pos hR]
      exact mul_le_mul_of_nonneg_left hcase hM₀0
    have h2 : M₀ * t₀ ≤ 8 * (M₀ + M₁ * R) * t₀ := by
      have h3 : M₀ ≤ 8 * (M₀ + M₁ * R) := by nlinarith [mul_nonneg hM₁0 hR.le]
      exact mul_le_mul_of_nonneg_right h3 ht₀.le
    calc ‖∫ t in (0 : ℝ)..R, A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)‖
        ≤ M₀ * |R - 0| := hbig
      _ ≤ M₀ * t₀ := h1
      _ ≤ 8 * (M₀ + M₁ * R) * t₀ := h2
  · rw [not_le] at hcase   -- t₀ < R
    have ht₀R : t₀ ≤ R := hcase.le
    have ht₀Icc : Set.uIcc t₀ R ⊆ Set.Icc 0 R := by
      rw [Set.uIcc_of_le ht₀R]
      exact Set.Icc_subset_Icc ht₀.le le_rfl
    have hheadIcc : Set.uIcc (0 : ℝ) t₀ ⊆ Set.Icc 0 R := by
      rw [Set.uIcc_of_le ht₀.le]
      exact Set.Icc_subset_Icc le_rfl ht₀R
    -- the coefficient of the phase derivative
    set c : ℂ := 2 * Complex.I * (ℓ : ℂ) with hc_def
    have hcne : c ≠ 0 := by
      rw [hc_def]
      exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
        (Complex.ofReal_ne_zero.mpr hℓ0.ne')
    have hnormc : ‖c‖ = 2 * ℓ := by
      rw [hc_def, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hℓ0]
      norm_num
    -- IBP data on [t₀, R]
    set u : ℝ → ℂ := fun t => A t * (c * (t : ℂ))⁻¹ with hu_def
    set u' : ℝ → ℂ := fun t => A' t * (c * (t : ℂ))⁻¹ - A t * (c * (t : ℂ) ^ 2)⁻¹ with hu'_def
    set v : ℝ → ℂ := fun t => Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2) with hv_def
    set v' : ℝ → ℂ := fun t => c * (t : ℂ) * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)
      with hv'_def
    have hinv_c : ContinuousOn (fun t : ℝ => (c * (t : ℂ))⁻¹) (Set.uIcc t₀ R) := by
      apply ContinuousOn.inv₀
      · fun_prop
      · intro x hx
        rw [Set.uIcc_of_le ht₀R] at hx
        exact mul_ne_zero hcne (Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le ht₀ hx.1).ne')
    have hu_cont : ContinuousOn u (Set.uIcc t₀ R) := (hAc.mono ht₀Icc).mul hinv_c
    have hv_cont : ContinuousOn v (Set.uIcc t₀ R) := hphase_c.continuousOn
    have huu' : ∀ x ∈ Set.Ioo (min t₀ R) (max t₀ R), HasDerivAt u (u' x) x := by
      intro x hx
      rw [min_eq_left ht₀R, max_eq_right ht₀R] at hx
      have hx0 : (0 : ℝ) < x := lt_trans ht₀ hx.1
      have hxIcc : x ∈ Set.Icc (0 : ℝ) R := ⟨hx0.le, hx.2.le⟩
      have hd := (hA x hxIcc).mul (hasDerivAt_invLin hcne hx0.ne')
      have hgoal : u' x = A' x * (c * (x : ℂ))⁻¹ + A x * -(c * (x : ℂ) ^ 2)⁻¹ := by
        rw [hu'_def]; ring
      rw [hu_def, hgoal]
      exact hd
    have hvv' : ∀ x ∈ Set.Ioo (min t₀ R) (max t₀ R), HasDerivAt v (v' x) x := by
      intro x _
      have hd := hasDerivAt_phase ℓ x
      have hgoal : v' x = 2 * Complex.I * ℓ * x * Complex.exp (Complex.I * ℓ * (x : ℂ) ^ 2) := by
        rw [hv'_def, hc_def]
      rw [hv_def, hgoal]
      exact hd
    have hu'_cont : ContinuousOn u' (Set.uIcc t₀ R) := by
      apply ContinuousOn.sub
      · exact (hA'c.mono ht₀Icc).mul hinv_c
      · apply ContinuousOn.mul (hAc.mono ht₀Icc)
        apply ContinuousOn.inv₀
        · fun_prop
        · intro x hx
          rw [Set.uIcc_of_le ht₀R] at hx
          have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ht₀ hx.1
          refine mul_ne_zero hcne ?_
          rw [← Complex.ofReal_pow]
          exact Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 hx0.ne')
    have hu'int : IntervalIntegrable u' volume t₀ R := hu'_cont.intervalIntegrable
    have hv'int : IntervalIntegrable v' volume t₀ R := by
      apply ContinuousOn.intervalIntegrable
      rw [hv'_def]
      fun_prop
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hu_cont hv_cont huu' hvv' hu'int hv'int
    -- the tail integrand is u·v'
    have htail_eq : (∫ t in t₀..R, A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2))
        = ∫ t in t₀..R, u t * v' t := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le ht₀R] at hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ht₀ hx.1
      have hne : c * (x : ℂ) ≠ 0 :=
        mul_ne_zero hcne (Complex.ofReal_ne_zero.mpr hx0.ne')
      simp only [hu_def, hv'_def]
      have hcancel : (c * (x : ℂ))⁻¹
            * (c * (x : ℂ) * Complex.exp (Complex.I * ℓ * (x : ℂ) ^ 2))
          = Complex.exp (Complex.I * ℓ * (x : ℂ) ^ 2) := by
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      rw [mul_assoc (A x), hcancel]
    -- split the integral
    have hint1 : IntervalIntegrable
        (fun t : ℝ => A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)) volume 0 t₀ :=
      (hIc.mono hheadIcc).intervalIntegrable
    have hint2 : IntervalIntegrable
        (fun t : ℝ => A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)) volume t₀ R :=
      (hIc.mono ht₀Icc).intervalIntegrable
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    -- head bound
    have hhead : ‖∫ t in (0 : ℝ)..t₀, A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)‖
        ≤ M₀ * t₀ := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := M₀) (a := (0 : ℝ)) (b := t₀)
        (f := fun t : ℝ => A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)) ?_
      · calc ‖∫ t in (0 : ℝ)..t₀, A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)‖
            ≤ M₀ * |t₀ - 0| := h
          _ = M₀ * t₀ := by rw [sub_zero, abs_of_pos ht₀]
      · intro x hx
        rw [Set.uIoc_of_le ht₀.le] at hx
        exact hIbnd x ⟨hx.1.le, hx.2.trans ht₀R⟩
    -- norms of the inverse factors
    have hnorm_inv1 : ∀ x : ℝ, 0 < x → ‖(c * (x : ℂ))⁻¹‖ = (2 * ℓ * x)⁻¹ := by
      intro x hx0
      rw [norm_inv, norm_mul, hnormc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    have hnorm_inv2 : ∀ x : ℝ, 0 < x → ‖(c * (x : ℂ) ^ 2)⁻¹‖ = (2 * ℓ * x ^ 2)⁻¹ := by
      intro x hx0
      rw [norm_inv, norm_mul, hnormc, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hx0]
    -- the constant identity (2ℓt₀)⁻¹ = t₀/2
    have h2lt : (2 * ℓ * t₀)⁻¹ = t₀ / 2 := by
      rw [mul_assoc, hℓt₀, ht₀_def, mul_inv]
      ring
    -- inverse monotonicity on [t₀, ∞)
    have hmono : ∀ x : ℝ, t₀ ≤ x → (2 * ℓ * x)⁻¹ ≤ (2 * ℓ * t₀)⁻¹ := by
      intro x hx
      have h1 : 0 < 2 * ℓ * t₀ := by positivity
      have h2 : 2 * ℓ * t₀ ≤ 2 * ℓ * x := by nlinarith
      exact inv_anti₀ h1 h2
    -- boundary-term bound: for t₀ ≤ x ≤ R, ‖u x · v x‖ ≤ M₀·t₀/2
    have hbound_pt : ∀ x : ℝ, t₀ ≤ x → x ∈ Set.Icc (0 : ℝ) R →
        ‖u x * v x‖ ≤ M₀ * (t₀ / 2) := by
      intro x hx hxIcc
      have hx0 : 0 < x := lt_of_lt_of_le ht₀ hx
      have hv1 : ‖v x‖ = 1 := by rw [hv_def]; exact norm_phase ℓ x
      rw [norm_mul, hv1, mul_one, hu_def]
      calc ‖A x * (c * (x : ℂ))⁻¹‖ = ‖A x‖ * (2 * ℓ * x)⁻¹ := by
            rw [norm_mul, hnorm_inv1 x hx0]
        _ ≤ M₀ * (2 * ℓ * x)⁻¹ :=
            mul_le_mul_of_nonneg_right (hM₀ x hxIcc) (by positivity)
        _ ≤ M₀ * (2 * ℓ * t₀)⁻¹ :=
            mul_le_mul_of_nonneg_left (hmono x hx) hM₀0
        _ = M₀ * (t₀ / 2) := by rw [h2lt]
    -- interior integrand bound
    set g : ℝ → ℝ := fun t => M₁ * (2 * ℓ)⁻¹ * t⁻¹ + M₀ * (2 * ℓ)⁻¹ * (t ^ 2)⁻¹ with hg_def
    have hpt : ∀ t ∈ Set.Ioc t₀ R, ‖u' t * v t‖ ≤ g t := by
      intro x hx
      have hx0 : 0 < x := lt_trans ht₀ hx.1
      have hxIcc : x ∈ Set.Icc (0 : ℝ) R := ⟨hx0.le, hx.2⟩
      have hv1 : ‖v x‖ = 1 := by rw [hv_def]; exact norm_phase ℓ x
      rw [norm_mul, hv1, mul_one, hu'_def]
      calc ‖A' x * (c * (x : ℂ))⁻¹ - A x * (c * (x : ℂ) ^ 2)⁻¹‖
          ≤ ‖A' x * (c * (x : ℂ))⁻¹‖ + ‖A x * (c * (x : ℂ) ^ 2)⁻¹‖ := norm_sub_le _ _
        _ = ‖A' x‖ * (2 * ℓ * x)⁻¹ + ‖A x‖ * (2 * ℓ * x ^ 2)⁻¹ := by
            rw [norm_mul, norm_mul, hnorm_inv1 x hx0, hnorm_inv2 x hx0]
        _ ≤ M₁ * (2 * ℓ * x)⁻¹ + M₀ * (2 * ℓ * x ^ 2)⁻¹ := by
            have b1 := mul_le_mul_of_nonneg_right (hM₁ x hxIcc)
              (by positivity : (0 : ℝ) ≤ (2 * ℓ * x)⁻¹)
            have b2 := mul_le_mul_of_nonneg_right (hM₀ x hxIcc)
              (by positivity : (0 : ℝ) ≤ (2 * ℓ * x ^ 2)⁻¹)
            linarith
        _ = g x := by simp only [hg_def]; ring
    have hg_cont : ContinuousOn g (Set.uIcc t₀ R) := by
      rw [Set.uIcc_of_le ht₀R]
      apply ContinuousOn.add
      · exact continuousOn_const.mul (continuousOn_id.inv₀ fun x hx =>
          (lt_of_lt_of_le ht₀ hx.1).ne')
      · exact continuousOn_const.mul ((continuousOn_id.pow 2).inv₀ fun x hx =>
          pow_ne_zero 2 (lt_of_lt_of_le ht₀ hx.1).ne')
    have hg_int : IntervalIntegrable g volume t₀ R := hg_cont.intervalIntegrable
    have hIle : ‖∫ t in t₀..R, u' t * v t‖ ≤ ∫ t in t₀..R, g t :=
      intervalIntegral.norm_integral_le_of_norm_le ht₀R
        (Filter.Eventually.of_forall fun x hx => hpt x hx) hg_int
    -- compute ∫ g
    have h0mem : (0 : ℝ) ∉ Set.uIcc t₀ R := by
      rw [Set.uIcc_of_le ht₀R]
      intro h
      exact absurd h.1 (not_le.mpr ht₀)
    have hint_inv : (∫ t in t₀..R, t⁻¹) = Real.log (R / t₀) := integral_inv h0mem
    have hint_sq : (∫ t in t₀..R, (t ^ 2)⁻¹) = t₀⁻¹ - R⁻¹ := by
      have hd : ∀ x ∈ Set.uIcc t₀ R, HasDerivAt (fun y : ℝ => -y⁻¹) ((x ^ 2)⁻¹) x := by
        intro x hx
        rw [Set.uIcc_of_le ht₀R] at hx
        have hx0 : x ≠ 0 := (lt_of_lt_of_le ht₀ hx.1).ne'
        have hd0 : HasDerivAt (fun y : ℝ => -y⁻¹) (-(-(x ^ 2)⁻¹)) x :=
          (hasDerivAt_inv hx0).neg
        rw [neg_neg] at hd0
        exact hd0
      have hcont : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume t₀ R := by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le ht₀R]
        exact (continuousOn_id.pow 2).inv₀ fun x hx =>
          pow_ne_zero 2 (lt_of_lt_of_le ht₀ hx.1).ne'
      have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont
      rw [heq]
      change -R⁻¹ - -t₀⁻¹ = t₀⁻¹ - R⁻¹
      ring
    have hga : IntervalIntegrable (fun t : ℝ => M₁ * (2 * ℓ)⁻¹ * t⁻¹) volume t₀ R := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ht₀R]
      exact continuousOn_const.mul (continuousOn_id.inv₀ fun x hx =>
        (lt_of_lt_of_le ht₀ hx.1).ne')
    have hgb : IntervalIntegrable (fun t : ℝ => M₀ * (2 * ℓ)⁻¹ * (t ^ 2)⁻¹) volume t₀ R := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le ht₀R]
      exact continuousOn_const.mul ((continuousOn_id.pow 2).inv₀ fun x hx =>
        pow_ne_zero 2 (lt_of_lt_of_le ht₀ hx.1).ne')
    have hg_val : (∫ t in t₀..R, g t)
        = M₁ * (2 * ℓ)⁻¹ * Real.log (R / t₀) + M₀ * (2 * ℓ)⁻¹ * (t₀⁻¹ - R⁻¹) := by
      rw [hg_def]
      rw [intervalIntegral.integral_add hga hgb, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, hint_inv, hint_sq]
    -- bound ∫ g
    have hlog : Real.log (R / t₀) ≤ R * Real.sqrt ℓ := by
      have h1 : 0 < R / t₀ := div_pos hR ht₀
      have h2 : R / t₀ = R * Real.sqrt ℓ := by rw [ht₀_def, div_inv_eq_mul]
      calc Real.log (R / t₀) ≤ R / t₀ - 1 := Real.log_le_sub_one_of_pos h1
        _ ≤ R / t₀ := by linarith
        _ = R * Real.sqrt ℓ := h2
    have hInterior : ‖∫ t in t₀..R, u' t * v t‖ ≤ M₁ * R * (t₀ / 2) + M₀ * (t₀ / 2) := by
      have hA1 : M₁ * (2 * ℓ)⁻¹ * Real.log (R / t₀) ≤ M₁ * R * (t₀ / 2) := by
        calc M₁ * (2 * ℓ)⁻¹ * Real.log (R / t₀)
            ≤ M₁ * (2 * ℓ)⁻¹ * (R * Real.sqrt ℓ) := by
              apply mul_le_mul_of_nonneg_left hlog (by positivity)
          _ = M₁ * R * ((2 * ℓ)⁻¹ * Real.sqrt ℓ) := by ring
          _ = M₁ * R * (t₀ / 2) := by rw [hkey]
      have hA2 : M₀ * (2 * ℓ)⁻¹ * (t₀⁻¹ - R⁻¹) ≤ M₀ * (t₀ / 2) := by
        have h1 : t₀⁻¹ - R⁻¹ ≤ t₀⁻¹ := by
          have : (0 : ℝ) ≤ R⁻¹ := by positivity
          linarith
        calc M₀ * (2 * ℓ)⁻¹ * (t₀⁻¹ - R⁻¹) ≤ M₀ * (2 * ℓ)⁻¹ * t₀⁻¹ := by
              apply mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = M₀ * ((2 * ℓ)⁻¹ * Real.sqrt ℓ) := by rw [ht₀inv]; ring
          _ = M₀ * (t₀ / 2) := by rw [hkey]
      calc ‖∫ t in t₀..R, u' t * v t‖ ≤ ∫ t in t₀..R, g t := hIle
        _ = M₁ * (2 * ℓ)⁻¹ * Real.log (R / t₀) + M₀ * (2 * ℓ)⁻¹ * (t₀⁻¹ - R⁻¹) := hg_val
        _ ≤ M₁ * R * (t₀ / 2) + M₀ * (t₀ / 2) := by linarith
    -- tail bound via IBP
    have htail : ‖∫ t in t₀..R, A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)‖
        ≤ M₀ * (t₀ / 2) + M₀ * (t₀ / 2) + (M₁ * R * (t₀ / 2) + M₀ * (t₀ / 2)) := by
      rw [htail_eq, hibp]
      have hbR := hbound_pt R ht₀R ⟨hR.le, le_rfl⟩
      have hbt₀ := hbound_pt t₀ le_rfl ⟨ht₀.le, ht₀R⟩
      calc ‖u R * v R - u t₀ * v t₀ - ∫ t in t₀..R, u' t * v t‖
          ≤ ‖u R * v R - u t₀ * v t₀‖ + ‖∫ t in t₀..R, u' t * v t‖ := norm_sub_le _ _
        _ ≤ ‖u R * v R‖ + ‖u t₀ * v t₀‖ + ‖∫ t in t₀..R, u' t * v t‖ := by
            linarith [norm_sub_le (u R * v R) (u t₀ * v t₀)]
        _ ≤ M₀ * (t₀ / 2) + M₀ * (t₀ / 2) + (M₁ * R * (t₀ / 2) + M₀ * (t₀ / 2)) := by
            linarith [hInterior]
    -- total
    calc ‖∫ t in (0 : ℝ)..R, A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)‖
        = ‖(∫ t in (0 : ℝ)..t₀, A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2))
            + ∫ t in t₀..R, A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)‖ := by
          rw [hsplit]
      _ ≤ ‖∫ t in (0 : ℝ)..t₀, A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)‖
            + ‖∫ t in t₀..R, A t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)‖ :=
          norm_add_le _ _
      _ ≤ M₀ * t₀ + (M₀ * (t₀ / 2) + M₀ * (t₀ / 2) + (M₁ * R * (t₀ / 2) + M₀ * (t₀ / 2))) := by
          linarith [hhead, htail]
      _ ≤ 8 * (M₀ + M₁ * R) * t₀ := by
          nlinarith [mul_nonneg hM₀0 ht₀.le, mul_nonneg (mul_nonneg hM₁0 hR.le) ht₀.le]

/-! ### The estimate for a second-order vanishing amplitude

For amplitudes vanishing to second order — `t²·C(t)` with `C` vanishing at the right endpoint —
one integration by parts against `d/dt[exp(iℓt²)]/(2iℓt)` peels the `t²` with no boundary terms
(the `t`-factor kills `t = 0`, `C(R) = 0` kills `t = R`), gaining a full power of `ℓ` over
`fresnel_core`: the bound is `O(ℓ^{−3/2})`.  This applies, for example, to an integrand
`B(t) = t²·s(t²)·W(t²)` when the stated derivative and endpoint conditions hold. -/

/-- **Decay for a second-order vanishing amplitude.** For `C` with two continuous derivatives on `[0, R]`,
bounds `N₀, N₁, N₂`, and `C(R) = 0`, the second-order-vanishing amplitude `t²·C(t)` satisfies
`‖∫₀^R t²·C(t)·exp(iℓt²) dt‖ ≤ 4(N₀ + 3N₁R + N₂R²)·ℓ^{−3/2}` for `ℓ ≥ 1`. -/
theorem fresnel_peel {C C' C'' : ℝ → ℂ} {R N₀ N₁ N₂ ℓ : ℝ} (hR : 0 < R)
    (hC : ∀ t ∈ Set.Icc (0 : ℝ) R, HasDerivAt C (C' t) t)
    (hC' : ∀ t ∈ Set.Icc (0 : ℝ) R, HasDerivAt C' (C'' t) t)
    (hC''c : ContinuousOn C'' (Set.Icc 0 R))
    (hN₀ : ∀ t ∈ Set.Icc (0 : ℝ) R, ‖C t‖ ≤ N₀)
    (hN₁ : ∀ t ∈ Set.Icc (0 : ℝ) R, ‖C' t‖ ≤ N₁)
    (hN₂ : ∀ t ∈ Set.Icc (0 : ℝ) R, ‖C'' t‖ ≤ N₂)
    (hCR : C R = 0) (hℓ : 1 ≤ ℓ) :
    ‖∫ t in (0 : ℝ)..R, (t : ℂ) ^ 2 * C t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)‖
      ≤ 4 * (N₀ + 3 * N₁ * R + N₂ * R ^ 2) * ((Real.sqrt ℓ)⁻¹ * ℓ⁻¹) := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hCcont : ContinuousOn C (Set.Icc 0 R) := fun t ht =>
    (hC t ht).continuousAt.continuousWithinAt
  have hC'cont : ContinuousOn C' (Set.Icc 0 R) := fun t ht =>
    (hC' t ht).continuousAt.continuousWithinAt
  have hphase_c : Continuous fun t : ℝ => Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2) := by
    fun_prop
  -- the peeled amplitude and its derivative
  set A : ℝ → ℂ := fun t => C t + (t : ℂ) * C' t with hA_def
  set A' : ℝ → ℂ := fun t => 2 * C' t + (t : ℂ) * C'' t with hA'_def
  have hAd : ∀ t ∈ Set.Icc (0 : ℝ) R, HasDerivAt A (A' t) t := by
    intro x hx
    have h1 : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have h2 := h1.mul (hC' x hx)
    have h3 := (hC x hx).add h2
    have heq : C' x + (1 * C' x + (x : ℂ) * C'' x) = A' x := by
      rw [hA'_def]; ring
    rw [heq] at h3
    exact h3
  have hAc : ContinuousOn A (Set.Icc 0 R) := fun t ht =>
    (hAd t ht).continuousAt.continuousWithinAt
  have hA'c : ContinuousOn A' (Set.Icc 0 R) := by
    rw [hA'_def]
    exact (continuousOn_const.mul hC'cont).add
      (Complex.continuous_ofReal.continuousOn.mul hC''c)
  -- bounds on the peeled amplitude
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hMA0 : ∀ t ∈ Set.Icc (0 : ℝ) R, ‖A t‖ ≤ N₀ + N₁ * R := by
    intro t ht
    rw [hA_def]
    have h3 : |t| * ‖C' t‖ ≤ R * N₁ := by
      rw [abs_of_nonneg ht.1]
      exact mul_le_mul ht.2 (hN₁ t ht) (norm_nonneg _) hR.le
    calc ‖C t + (t : ℂ) * C' t‖ ≤ ‖C t‖ + ‖(t : ℂ) * C' t‖ := norm_add_le _ _
      _ = ‖C t‖ + |t| * ‖C' t‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ N₀ + R * N₁ := by linarith [hN₀ t ht]
      _ = N₀ + N₁ * R := by ring
  have hMA1 : ∀ t ∈ Set.Icc (0 : ℝ) R, ‖A' t‖ ≤ 2 * N₁ + N₂ * R := by
    intro t ht
    rw [hA'_def]
    have h3 : |t| * ‖C'' t‖ ≤ R * N₂ := by
      rw [abs_of_nonneg ht.1]
      exact mul_le_mul ht.2 (hN₂ t ht) (norm_nonneg _) hR.le
    calc ‖2 * C' t + (t : ℂ) * C'' t‖ ≤ ‖2 * C' t‖ + ‖(t : ℂ) * C'' t‖ := norm_add_le _ _
      _ = 2 * ‖C' t‖ + |t| * ‖C'' t‖ := by
          rw [norm_mul, norm_mul, h2n, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 * N₁ + R * N₂ := by
          have h1 := hN₁ t ht
          linarith
      _ = 2 * N₁ + N₂ * R := by ring
  -- the core estimate on the peeled amplitude
  have hcore := fresnel_core hR hAd hA'c hMA0 hMA1 hℓ
  -- IBP data
  set c : ℂ := 2 * Complex.I * (ℓ : ℂ) with hc_def
  have hcne : c ≠ 0 := by
    rw [hc_def]
    exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr hℓ0.ne')
  have hnormc : ‖c‖ = 2 * ℓ := by
    rw [hc_def, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hℓ0]
    norm_num
  set u : ℝ → ℂ := fun t => (t : ℂ) * C t * c⁻¹ with hu_def
  set u' : ℝ → ℂ := fun t => A t * c⁻¹ with hu'_def
  set v : ℝ → ℂ := fun t => Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2) with hv_def
  set v' : ℝ → ℂ := fun t => c * (t : ℂ) * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2)
    with hv'_def
  have hu_cont : ContinuousOn u (Set.uIcc 0 R) := by
    rw [Set.uIcc_of_le hR.le, hu_def]
    exact (Complex.continuous_ofReal.continuousOn.mul hCcont).mul continuousOn_const
  have hv_cont : ContinuousOn v (Set.uIcc 0 R) := hphase_c.continuousOn
  have huu' : ∀ x ∈ Set.Ioo (min 0 R) (max 0 R), HasDerivAt u (u' x) x := by
    intro x hx
    rw [min_eq_left hR.le, max_eq_right hR.le] at hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) R := ⟨hx.1.le, hx.2.le⟩
    have h1 : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have h2 := (h1.mul (hC x hxIcc)).mul_const c⁻¹
    have heq : (1 * C x + (x : ℂ) * C' x) * c⁻¹ = u' x := by
      rw [hu'_def, hA_def]; ring
    rw [heq] at h2
    exact h2
  have hvv' : ∀ x ∈ Set.Ioo (min 0 R) (max 0 R), HasDerivAt v (v' x) x := by
    intro x _
    have hd := hasDerivAt_phase ℓ x
    have hgoal : v' x = 2 * Complex.I * ℓ * x * Complex.exp (Complex.I * ℓ * (x : ℂ) ^ 2) := by
      rw [hv'_def, hc_def]
    rw [hv_def, hgoal]
    exact hd
  have hu'int : IntervalIntegrable u' volume 0 R := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hR.le, hu'_def]
    exact hAc.mul continuousOn_const
  have hv'int : IntervalIntegrable v' volume 0 R := by
    apply ContinuousOn.intervalIntegrable
    rw [hv'_def]
    fun_prop
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu_cont hv_cont huu' hvv' hu'int hv'int
  -- the goal integrand is u·v'
  have hgoal_eq : (∫ t in (0 : ℝ)..R, (t : ℂ) ^ 2 * C t * Complex.exp (Complex.I * ℓ * (t : ℂ) ^ 2))
      = ∫ t in (0 : ℝ)..R, u t * v' t := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hu_def, hv'_def]
    have hcc : c⁻¹ * c = 1 := inv_mul_cancel₀ hcne
    calc (x : ℂ) ^ 2 * C x * Complex.exp (Complex.I * ℓ * (x : ℂ) ^ 2)
        = (c⁻¹ * c) * ((x : ℂ) ^ 2 * C x * Complex.exp (Complex.I * ℓ * (x : ℂ) ^ 2)) := by
          rw [hcc, one_mul]
      _ = (x : ℂ) * C x * c⁻¹ * (c * (x : ℂ) * Complex.exp (Complex.I * ℓ * (x : ℂ) ^ 2)) := by
          ring
  -- boundary terms vanish
  have hu0 : u 0 = 0 := by
    rw [hu_def]
    simp
  have huR : u R = 0 := by
    rw [hu_def]
    simp [hCR]
  -- pull the constant out of the remaining integral
  have hpull : (∫ t in (0 : ℝ)..R, u' t * v t)
      = c⁻¹ * ∫ t in (0 : ℝ)..R, A t * v t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hu'_def]
    ring
  rw [hgoal_eq, hibp, huR, hu0, zero_mul, zero_mul, sub_zero, zero_sub, norm_neg, hpull,
    norm_mul, norm_inv, hnormc]
  calc (2 * ℓ)⁻¹ * ‖∫ t in (0 : ℝ)..R, A t * v t‖
      ≤ (2 * ℓ)⁻¹ * (8 * ((N₀ + N₁ * R) + (2 * N₁ + N₂ * R) * R) * (Real.sqrt ℓ)⁻¹) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = 4 * (N₀ + 3 * N₁ * R + N₂ * R ^ 2) * ((Real.sqrt ℓ)⁻¹ * ℓ⁻¹) := by
        rw [mul_inv]
        ring

/-! ### The substitution x = t² -/

/-- **The `x = t²` change of variables**: for `G` continuous on `[0, L]`,
`∫₀^L G(x) dx = ∫₀^{√L} 2t·G(t²) dt`.  Phase-agnostic: applied to `G(x) = g(x)·exp(iℓx)` it
converts the linear-phase edge integral into the quadratic-phase form consumed by
`fresnel_core`/`fresnel_peel`. -/
theorem fresnel_cov {G : ℝ → ℂ} {L : ℝ} (hL : 0 < L) (hG : ContinuousOn G (Set.Icc 0 L)) :
    (∫ x in (0 : ℝ)..L, G x)
      = ∫ t in (0 : ℝ)..Real.sqrt L, ((2 * t : ℝ) : ℂ) * G (t ^ 2) := by
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hf : ∀ t ∈ Set.uIcc (0 : ℝ) (Real.sqrt L),
      HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    intro t _
    simpa using hasDerivAt_pow 2 t
  have hf' : ContinuousOn (fun t : ℝ => 2 * t) (Set.uIcc 0 (Real.sqrt L)) := by fun_prop
  have himg : (fun t : ℝ => t ^ 2) '' Set.uIcc 0 (Real.sqrt L) ⊆ Set.Icc 0 L := by
    rw [Set.uIcc_of_le hsL.le]
    rintro x ⟨t, ht, rfl⟩
    exact ⟨sq_nonneg t, by nlinarith [Real.sq_sqrt hL.le, ht.1, ht.2]⟩
  have hcov := intervalIntegral.integral_deriv_smul_comp' hf hf' (hG.mono himg)
  have h0 : ((0 : ℝ) ^ 2 : ℝ) = 0 := by norm_num
  have hL2 : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hL.le
  rw [h0, hL2] at hcov
  rw [← hcov]
  apply intervalIntegral.integral_congr
  intro t _
  simp [Complex.real_smul]

end KsIndex.Fresnel
