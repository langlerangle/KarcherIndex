module

/-
KsIndexLean — Frequency decay of the junction Fourier coefficients.

For `η > 0`, the substitution `x = t²` writes `Jp η ξ` as the quadratic-phase
integral of `t² * Camp η t * exp (iξt²)` on `0..sqrt (πη)`.
The identity `sqrt (sin (t²)) = t * sqrt (sinc (t²))` for `t ≥ 0` supplies
the amplitude in these coordinates.

For `0 < η ≤ 1/4` and `ξ ≥ 1`, the derivative bounds from `JunctionAmp`,
continuity of the second derivative, and vanishing of the amplitude at the
upper endpoint allow application of `fresnel_peel`. This gives
`‖Jp η ξ‖ ≤ 4 * CJfr * (sqrt ξ)⁻¹ * ξ⁻¹`, where
`CJfr = 200 * (1 + Mψ + Mψ₂)` is independent of `η` and `ξ`.
Real amplitudes and conjugation extend the bound to `Jm` and to `|ξ| ≥ 1`.

Combining the two integrals yields
`‖fc (fJ η) ℓ‖ ≤ (2π)⁻¹ * 8 * CJfr * (sqrt |ξ|)⁻¹ * |ξ|⁻¹`
for `ξ = ℓ+1/2`, `|ξ| ≥ 1`, and `0 < η ≤ 1/4`.
The two frequencies `ℓ = 0,-1` are outside this tail estimate; the
frequency-independent head bound is supplied by `ArcJunction`.
-/
public import KsIndexLean.JunctionAmp
public import KsIndexLean.Fresnel

@[expose] public section


noncomputable section

open Real Set MeasureTheory intervalIntegral
open KsIndex.SincKit KsIndex.JunctionCut KsIndex.ArcJunction KsIndex.JunctionAmp
  KsIndex.Fresnel
open KsIndex.PunctureCutoff KsIndex.CutLaplacian

namespace KsIndex.JunctionFresnel

/-- The junction Fresnel constant `200·(1 + Mψ + Mψ₂)`. -/
def CJfr : ℝ := 200 * (1 + Mψ + Mψ₂)

lemma CJfr_nonneg : 0 ≤ CJfr := by
  have := Mψ_nonneg
  have := Mψ₂_nonneg
  unfold CJfr
  nlinarith

/-! ### The √-desingularization -/

lemma sin_eq_mul_sinc (y : ℝ) : Real.sin y = y * Real.sinc y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [Real.sinc_of_ne_zero hy, mul_comm, div_mul_cancel₀ _ hy]

lemma sqrt_sin_sq {t : ℝ} (ht0 : 0 ≤ t) : Real.sqrt (Real.sin (t ^ 2)) = t * s (t ^ 2) := by
  rw [sin_eq_mul_sinc, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht0]
  rfl

/-! ### The change of variables onto the peeled form -/

lemma Jp_eq_peel (η ξ : ℝ) (hη0 : 0 < η) :
    Jp η ξ = ∫ t in (0:ℝ)..Real.sqrt (π * η),
      (t : ℂ) ^ 2 * ((Camp η t : ℝ) : ℂ) * Complex.exp (Complex.I * (ξ : ℂ) * (t : ℂ) ^ 2) := by
  rw [Jp, fresnel_cov (by positivity : (0:ℝ) < π * η)
    (continuous_Jp_integrand η ξ).continuousOn]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le (Real.sqrt_nonneg _)] at ht
  rw [sqrt_sin_sq ht.1]
  simp only [Camp]
  push_cast
  ring_nf

/-! ### Continuity of the second-derivative amplitude -/

lemma continuous_s : Continuous s := Real.continuous_sqrt.comp Real.continuous_sinc

lemma continuous_wJ1 (η : ℝ) : Continuous (wJ1 η) := by
  have hdψ : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  exact ((hdψ.comp ((Real.continuous_sin.sub continuous_const).div_const η)).mul
    (Real.continuous_cos.div_const η)).neg

lemma continuous_wJ2 (η : ℝ) : Continuous (wJ2 η) := by
  have hdψ : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hd2ψ : Continuous (deriv (deriv Real.smoothTransition)) := by
    have hd1 : ContDiff ℝ 1 (deriv Real.smoothTransition) :=
      (contDiff_succ_iff_deriv.mp (Real.smoothTransition.contDiff (n := 2))).2.2
    exact hd1.continuous_deriv le_rfl
  have hinner : Continuous (fun x : ℝ => (Real.sin x - η) / η) :=
    (Real.continuous_sin.sub continuous_const).div_const η
  exact (((hd2ψ.comp hinner).mul (Real.continuous_cos.div_const η)).mul
      (Real.continuous_cos.div_const η)).add
    ((hdψ.comp hinner).mul ((Real.continuous_sin.neg).div_const η)) |>.neg

lemma continuousOn_ds : ContinuousOn ds (Set.Icc (0:ℝ) 1) := by
  refine ContinuousOn.div continuous_dsinc.continuousOn
    (continuous_const.mul continuous_s).continuousOn (fun y hy => ?_)
  exact mul_ne_zero two_ne_zero (s_pos hy.1 hy.2).ne'

lemma continuousOn_d2s : ContinuousOn d2s (Set.Icc (0:ℝ) 1) := by
  refine ContinuousOn.sub
    (ContinuousOn.div continuous_d2sinc.continuousOn
      (continuous_const.mul continuous_s).continuousOn (fun y hy => ?_))
    (ContinuousOn.div (continuous_dsinc.pow 2).continuousOn
      (continuous_const.mul (continuous_s.pow 3)).continuousOn (fun y hy => ?_))
  · exact mul_ne_zero two_ne_zero (s_pos hy.1 hy.2).ne'
  · exact mul_ne_zero (by norm_num) (pow_ne_zero 3 (s_pos hy.1 hy.2).ne')

lemma continuousOn_Camp2 (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) :
    ContinuousOn (Camp2 η) (Set.Icc (0:ℝ) (Real.sqrt (π * η))) := by
  have hRsq : Real.sqrt (π * η) ^ 2 = π * η := Real.sq_sqrt (by positivity)
  have hmaps : Set.MapsTo (fun t : ℝ => t ^ 2)
      (Set.Icc (0:ℝ) (Real.sqrt (π * η))) (Set.Icc (0:ℝ) 1) := by
    intro t htm
    refine ⟨sq_nonneg t, ?_⟩
    have hsq : t ^ 2 ≤ π * η := by nlinarith [htm.1, htm.2, hRsq]
    exact sq_le_one_of_le hη0 hη hsq
  have hsqc : ContinuousOn (fun t : ℝ => t ^ 2)
      (Set.Icc (0:ℝ) (Real.sqrt (π * η))) := (continuous_pow 2).continuousOn
  have hds_q : ContinuousOn (fun t : ℝ => ds (t ^ 2))
      (Set.Icc (0:ℝ) (Real.sqrt (π * η))) := continuousOn_ds.comp hsqc hmaps
  have hd2s_q : ContinuousOn (fun t : ℝ => d2s (t ^ 2))
      (Set.Icc (0:ℝ) (Real.sqrt (π * η))) := continuousOn_d2s.comp hsqc hmaps
  have hs_q : ContinuousOn (fun t : ℝ => s (t ^ 2))
      (Set.Icc (0:ℝ) (Real.sqrt (π * η))) :=
    (continuous_s.comp (continuous_pow 2)).continuousOn
  have hw_q : ContinuousOn (fun t : ℝ => wJ η (t ^ 2))
      (Set.Icc (0:ℝ) (Real.sqrt (π * η))) :=
    ((continuous_wJ η).comp (continuous_pow 2)).continuousOn
  have hw1_q : ContinuousOn (fun t : ℝ => wJ1 η (t ^ 2))
      (Set.Icc (0:ℝ) (Real.sqrt (π * η))) :=
    ((continuous_wJ1 η).comp (continuous_pow 2)).continuousOn
  have hw2_q : ContinuousOn (fun t : ℝ => wJ2 η (t ^ 2))
      (Set.Icc (0:ℝ) (Real.sqrt (π * η))) :=
    ((continuous_wJ2 η).comp (continuous_pow 2)).continuousOn
  have h2t : ContinuousOn (fun t : ℝ => 2 * t)
      (Set.Icc (0:ℝ) (Real.sqrt (π * η))) := (continuous_const.mul continuous_id).continuousOn
  show ContinuousOn (fun t : ℝ =>
      2 * ((d2s (t ^ 2) * (2 * t) * (2 * t) + ds (t ^ 2) * 2) * wJ η (t ^ 2)
        + ds (t ^ 2) * (2 * t) * (wJ1 η (t ^ 2) * (2 * t))
        + (ds (t ^ 2) * (2 * t) * (wJ1 η (t ^ 2) * (2 * t))
          + s (t ^ 2) * (wJ2 η (t ^ 2) * (2 * t) * (2 * t) + wJ1 η (t ^ 2) * 2))))
    (Set.Icc (0:ℝ) (Real.sqrt (π * η)))
  exact continuousOn_const.mul
    (((((hd2s_q.mul h2t).mul h2t).add (hds_q.mul continuousOn_const)).mul hw_q).add
      ((hds_q.mul h2t).mul (hw1_q.mul h2t)) |>.add
      (((hds_q.mul h2t).mul (hw1_q.mul h2t)).add
        (hs_q.mul (((hw2_q.mul h2t).mul h2t).add (hw1_q.mul continuousOn_const)))))

/-! ### The Fresnel bound at `ξ ≥ 1` -/

theorem norm_Jp_le_tail (η ξ : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) (hξ : 1 ≤ ξ) :
    ‖Jp η ξ‖ ≤ 4 * CJfr * ((Real.sqrt ξ)⁻¹ * ξ⁻¹) := by
  have hπ2 : π < 3.15 := Real.pi_lt_d2
  have hR : (0:ℝ) < Real.sqrt (π * η) := Real.sqrt_pos.mpr (by positivity)
  have hRsq : Real.sqrt (π * η) ^ 2 = π * η := Real.sq_sqrt (by positivity)
  have hmem_sq : ∀ t ∈ Set.Icc (0:ℝ) (Real.sqrt (π * η)), t ^ 2 ≤ π * η := by
    intro t htm
    calc t ^ 2 ≤ Real.sqrt (π * η) ^ 2 := by nlinarith [htm.1, htm.2]
      _ = π * η := hRsq
  have hmem_one : ∀ t ∈ Set.Icc (0:ℝ) (Real.sqrt (π * η)), t ^ 2 ≤ 1 := fun t htm =>
    sq_le_one_of_le hη0 hη (hmem_sq t htm)
  rw [Jp_eq_peel η ξ hη0]
  have hpeel := fresnel_peel (C := fun t => ((Camp η t : ℝ) : ℂ))
    (C' := fun t => ((Camp1 η t : ℝ) : ℂ)) (C'' := fun t => ((Camp2 η t : ℝ) : ℂ))
    (N₀ := 2) (N₁ := 4 * Real.sqrt (π * η) * (1 + Mψ / η))
    (N₂ := 50 * (1 + Mψ + Mψ₂) / η) hR
    (fun t htm => (hasDerivAt_Camp (hmem_one t htm)).ofReal_comp)
    (fun t htm => (hasDerivAt_Camp1 (hmem_one t htm)).ofReal_comp)
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_Camp2 η hη0 hη))
    (fun t htm => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_Camp_le hη0 hη (hmem_sq t htm))
    (fun t htm => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_Camp1_le hη0 hη htm.1 (hmem_sq t htm))
    (fun t htm => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_Camp2_le hη0 hη htm.1 (hmem_sq t htm))
    (by rw [Camp_root_eq_zero hη0 hη, Complex.ofReal_zero]) hξ
  refine le_trans hpeel ?_
  refine mul_le_mul_of_nonneg_right ?_
    (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr (by linarith)))
  -- the bracket collapse: 4·(N₀ + 3N₁R + N₂R²) ≤ 4·CJfr
  have hRR : Real.sqrt (π * η) * Real.sqrt (π * η) = π * η :=
    Real.mul_self_sqrt (by positivity)
  have e1 : 3 * (4 * Real.sqrt (π * η) * (1 + Mψ / η)) * Real.sqrt (π * η)
      = 12 * (π * η) + 12 * π * Mψ := by
    calc 3 * (4 * Real.sqrt (π * η) * (1 + Mψ / η)) * Real.sqrt (π * η)
        = 12 * (Real.sqrt (π * η) * Real.sqrt (π * η)) * (1 + Mψ / η) := by ring
      _ = 12 * (π * η) * (1 + Mψ / η) := by rw [hRR]
      _ = 12 * (π * η) + 12 * π * Mψ := by field_simp
  have e2 : 50 * (1 + Mψ + Mψ₂) / η * Real.sqrt (π * η) ^ 2
      = 50 * π * (1 + Mψ + Mψ₂) := by
    rw [hRsq]
    field_simp
  rw [e1, e2]
  have hπη : π * η ≤ 0.7875 := by nlinarith
  have hMπ : π * Mψ ≤ 3.15 * Mψ := mul_le_mul_of_nonneg_right hπ2.le Mψ_nonneg
  have hM2π : π * Mψ₂ ≤ 3.15 * Mψ₂ := mul_le_mul_of_nonneg_right hπ2.le Mψ₂_nonneg
  unfold CJfr
  nlinarith [Mψ_nonneg, Mψ₂_nonneg]

/-! ### Conjugation: the bound transfers to `J₋` and to negative frequencies -/

lemma intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    (∫ x in a..b, (starRingEnd ℂ) (f x)) = (starRingEnd ℂ) (∫ x in a..b, f x) := by
  simp only [intervalIntegral]
  rw [integral_conj, integral_conj, map_sub]

lemma Jm_eq_conj (η ξ : ℝ) : Jm η ξ = (starRingEnd ℂ) (Jp η ξ) := by
  rw [Jp, ← intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun x hx => ?_
  simp only [map_mul, Complex.conj_ofReal]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- `J₊` at the opposite frequency is `J₋`. -/
lemma Jp_neg_eq (η ξ : ℝ) : Jp η (-ξ) = Jm η ξ := by
  rw [Jp, Jm]
  refine intervalIntegral.integral_congr fun x hx => ?_
  congr 1
  congr 1
  push_cast
  ring

lemma Jm_neg_eq (η ξ : ℝ) : Jm η (-ξ) = Jp η ξ := by
  have h := Jp_neg_eq η (-ξ)
  rw [neg_neg] at h
  exact h.symm

/-- `J₊` obeys the tail bound at every frequency with `|ξ| ≥ 1`. -/
theorem norm_Jp_le_tail_abs (η ξ : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) (hξ : 1 ≤ |ξ|) :
    ‖Jp η ξ‖ ≤ 4 * CJfr * ((Real.sqrt |ξ|)⁻¹ * |ξ|⁻¹) := by
  rcases le_or_gt 0 ξ with h0 | h0
  · rw [abs_of_nonneg h0] at hξ ⊢
    exact norm_Jp_le_tail η ξ hη0 hη hξ
  · rw [abs_of_neg h0] at hξ ⊢
    have h := norm_Jp_le_tail η (-ξ) hη0 hη hξ
    rw [Jp_neg_eq] at h
    calc ‖Jp η ξ‖ = ‖(starRingEnd ℂ) (Jp η ξ)‖ := (RCLike.norm_conj _).symm
      _ = ‖Jm η ξ‖ := by rw [← Jm_eq_conj]
      _ ≤ 4 * CJfr * ((Real.sqrt (-ξ))⁻¹ * (-ξ)⁻¹) := h

/-- `J₋` obeys the tail bound at every frequency with `|ξ| ≥ 1`. -/
theorem norm_Jm_le_tail_abs (η ξ : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) (hξ : 1 ≤ |ξ|) :
    ‖Jm η ξ‖ ≤ 4 * CJfr * ((Real.sqrt |ξ|)⁻¹ * |ξ|⁻¹) := by
  have h := norm_Jp_le_tail_abs η ξ hη0 hη hξ
  calc ‖Jm η ξ‖ = ‖(starRingEnd ℂ) (Jp η ξ)‖ := by rw [Jm_eq_conj]
    _ = ‖Jp η ξ‖ := RCLike.norm_conj _
    _ ≤ _ := h

/-! ### The headline tail bound -/

/-- **The junction tail bound.**  For `0 < η ≤ 1/4` and `|ℓ + 1/2| ≥ 1`,
`‖fc (fJ η) ℓ‖ ≤ (2π)⁻¹·8·CJfr·(√|ξ|)⁻¹·|ξ|⁻¹` — the `O(|ℓ|^{−3/2})` envelope,
uniform for `0 < η ≤ 1/4`. -/
theorem norm_fc_fJ_le_tail (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1/4) (ℓ : ℤ)
    (hℓ : 1 ≤ |(ℓ : ℝ) + 1/2|) :
    ‖Parseval.fc (KsIndex.ArcField.fJ η) ℓ‖
      ≤ (2 * π : ℝ)⁻¹ * (8 * CJfr)
        * ((Real.sqrt |(ℓ : ℝ) + 1/2|)⁻¹ * |(ℓ : ℝ) + 1/2|⁻¹) := by
  have hπ := Real.pi_pos
  rw [fc_fJ_eq η hη0 hη ℓ]
  have hpre1 : ‖Complex.exp ((((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)‖ = 1 := by
    rw [show (((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I
        = (((((ℓ:ℝ) + 1/2) * (π/2) : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hpre2 : ‖Complex.exp (-(((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)‖ = 1 := by
    rw [show -(((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I
        = ((-(((ℓ:ℝ) + 1/2) * (π/2)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hm := norm_Jm_le_tail_abs η ((ℓ:ℝ) + 1/2) hη0 hη hℓ
  have hp := norm_Jp_le_tail_abs η ((ℓ:ℝ) + 1/2) hη0 hη hℓ
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < (2 * π)⁻¹)]
  have htail : ‖Complex.exp ((((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)
      * Jm η ((ℓ : ℝ) + 1/2)
      + Complex.exp (-(((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)
        * Jp η ((ℓ : ℝ) + 1/2)‖
      ≤ 8 * CJfr * ((Real.sqrt |(ℓ : ℝ) + 1/2|)⁻¹ * |(ℓ : ℝ) + 1/2|⁻¹) := by
    calc _ ≤ ‖Complex.exp ((((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)
            * Jm η ((ℓ : ℝ) + 1/2)‖
          + ‖Complex.exp (-(((ℓ : ℂ) + 1/2) * (π/2 : ℝ)) * Complex.I)
            * Jp η ((ℓ : ℝ) + 1/2)‖ := norm_add_le _ _
      _ = ‖Jm η ((ℓ : ℝ) + 1/2)‖ + ‖Jp η ((ℓ : ℝ) + 1/2)‖ := by
          rw [norm_mul, norm_mul, hpre1, hpre2, one_mul, one_mul]
      _ ≤ 4 * CJfr * ((Real.sqrt |(ℓ : ℝ) + 1/2|)⁻¹ * |(ℓ : ℝ) + 1/2|⁻¹)
          + 4 * CJfr * ((Real.sqrt |(ℓ : ℝ) + 1/2|)⁻¹ * |(ℓ : ℝ) + 1/2|⁻¹) :=
          add_le_add hm hp
      _ = 8 * CJfr * ((Real.sqrt |(ℓ : ℝ) + 1/2|)⁻¹ * |(ℓ : ℝ) + 1/2|⁻¹) := by ring
  calc (2 * π)⁻¹ * ‖_ + _‖
      ≤ (2 * π)⁻¹ * (8 * CJfr * ((Real.sqrt |(ℓ : ℝ) + 1/2|)⁻¹ * |(ℓ : ℝ) + 1/2|⁻¹)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
    _ = (2 * π : ℝ)⁻¹ * (8 * CJfr)
        * ((Real.sqrt |(ℓ : ℝ) + 1/2|)⁻¹ * |(ℓ : ℝ) + 1/2|⁻¹) := by ring

end KsIndex.JunctionFresnel
