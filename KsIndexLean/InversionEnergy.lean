module

public import KsIndexLean.InvertedRadialProfile

@[expose] public section


open Set MeasureTheory intervalIntegral

noncomputable section
namespace KsIndex.Trace

/-- Positive Jacobian version of the inversion substitution. -/
lemma integral_inv_jacobian (q : ℝ → ℝ) :
    (∫ r in (1 : ℝ)..2, (r ^ 2)⁻¹ * q r⁻¹) = ∫ t in (1 / 2 : ℝ)..1, q t := by
  have h := integral_invertedRadialDeriv q (by norm_num : (1 : ℝ) ≤ 2)
  simp only [invertedRadialDeriv, smul_eq_mul, neg_mul, intervalIntegral.integral_neg] at h
  have hs := integral_symm (μ := volume) (f := q) ((2 : ℝ)⁻¹) (1 : ℝ)
  rw [hs] at h
  simpa using neg_injective h

lemma inv_jacobian_integrable {q : ℝ → ℝ}
    (hq : IntervalIntegrable q volume (1 / 2) 1) :
    IntervalIntegrable (fun r => (r ^ 2)⁻¹ * q r⁻¹) volume 1 2 := by
  have hi := (invertedRadialDeriv_integrable hq).neg
  change IntervalIntegrable (fun r => -(invertedRadialDeriv q r)) volume 1 2 at hi
  simpa only [invertedRadialDeriv, smul_eq_mul, neg_mul, neg_neg] using hi

lemma inner_inv_sq_continuous :
    ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (uIcc (1 / 2) 1) := by
  rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  exact (continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero _ (by change t ≠ 0; linarith [ht.1]))

lemma integral_comp_inv (q : ℝ → ℝ) :
    (∫ r in (1 : ℝ)..2, q r⁻¹) = ∫ t in (1 / 2 : ℝ)..1, (t ^ 2)⁻¹ * q t := by
  rw [← integral_inv_jacobian (fun t => (t ^ 2)⁻¹ * q t)]
  apply integral_congr_Ioo_of_le (by norm_num : (1 : ℝ) ≤ 2)
  intro r hr
  have hn : r ≠ 0 := by linarith [hr.1]
  simp only [inv_pow, inv_inv]
  field_simp

lemma comp_inv_integrable {q : ℝ → ℝ}
    (hq : IntervalIntegrable q volume (1 / 2) 1) :
    IntervalIntegrable (fun r => q r⁻¹) volume 1 2 := by
  apply (inv_jacobian_integrable (hq.continuousOn_mul inner_inv_sq_continuous)).congr_uIoo
  rw [uIoo_of_le (by norm_num : (1 : ℝ) ≤ 2)]
  intro r hr
  have hn : r ≠ 0 := by linarith [hr.1]
  simp only [inv_pow, inv_inv]
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_invertedRadialDeriv_sq (g : ℝ → E) (r : ℝ) :
    ‖invertedRadialDeriv g r‖ ^ 2 = (r ^ 2)⁻¹ * ((r⁻¹) ^ 2 * ‖g r⁻¹‖ ^ 2) := by
  simp only [invertedRadialDeriv, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg r)), inv_pow]
  ring

lemma invertedRadialDeriv_sq_integrable {g : ℝ → E}
    (hg : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume (1 / 2) 1) :
    IntervalIntegrable (fun r => ‖invertedRadialDeriv g r‖ ^ 2) volume 1 2 := by
  simpa only [norm_invertedRadialDeriv_sq, Pi.pow_apply, id_eq] using
    inv_jacobian_integrable (hg.continuousOn_mul (continuousOn_id.pow 2))

lemma integral_invertedRadialDeriv_sq (g : ℝ → E) :
    (∫ r in (1 : ℝ)..2, ‖invertedRadialDeriv g r‖ ^ 2) =
      ∫ t in (1 / 2 : ℝ)..1, t ^ 2 * ‖g t‖ ^ 2 := by
  simp only [norm_invertedRadialDeriv_sq]
  exact integral_inv_jacobian (fun t => t ^ 2 * ‖g t‖ ^ 2)

lemma integral_invertedRadialDeriv_sq_le {g : ℝ → E}
    (hg : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume (1 / 2) 1) :
    (∫ r in (1 : ℝ)..2, ‖invertedRadialDeriv g r‖ ^ 2) ≤
      ∫ t in (1 / 2 : ℝ)..1, ‖g t‖ ^ 2 := by
  rw [integral_invertedRadialDeriv_sq]
  apply integral_mono_on (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (hg.continuousOn_mul (continuousOn_id.pow 2)) hg
  intro t ht
  have hsq : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  exact mul_le_of_le_one_left (sq_nonneg _) hsq

omit [NormedSpace ℝ E] in
lemma integral_comp_inv_sq_le {f : ℝ → E}
    (hf : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume (1 / 2) 1) :
    (∫ r in (1 : ℝ)..2, ‖f r⁻¹‖ ^ 2) ≤ 4 * ∫ t in (1 / 2 : ℝ)..1, ‖f t‖ ^ 2 := by
  rw [integral_comp_inv (fun t => ‖f t‖ ^ 2), ← intervalIntegral.integral_const_mul]
  apply integral_mono_on (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (hf.continuousOn_mul inner_inv_sq_continuous) (hf.const_mul 4)
  intro t ht
  have hp : 0 < t ^ 2 := sq_pos_of_pos (by linarith [ht.1])
  have hb : (t ^ 2)⁻¹ ≤ 4 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hp).mpr (by nlinarith [ht.1])
  exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)

omit [NormedSpace ℝ E] in
lemma joinAt_sq_integrable {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) {f g : ℝ → E}
    (hf : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume a c)
    (hg : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume c b) :
    IntervalIntegrable (fun t => ‖joinAt c f g t‖ ^ 2) volume a b := by
  apply (joinAt_integrable hac hcb hf hg).congr_uIoo
  intro t _
  simp only [joinAt]
  split_ifs <;> rfl

end KsIndex.Trace
