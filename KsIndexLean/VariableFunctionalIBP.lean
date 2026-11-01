module

public import KsIndexLean.BanachIntervalFTC
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section


open Set Filter MeasureTheory AbsolutelyContinuousOnInterval

noncomputable section
namespace KsIndex.Trace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Applying a varying absolutely continuous bounded operator preserves absolute continuity. -/
theorem absolutelyContinuous_clm_apply {L : ℝ → E →L[ℝ] F} {f : ℝ → E} {a b : ℝ}
    (hL : AbsolutelyContinuousOnInterval L a b)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => L t (f t)) a b := by
  obtain ⟨C, hC⟩ := hL.exists_bound
  obtain ⟨D, hD⟩ := hf.exists_bound
  unfold AbsolutelyContinuousOnInterval at hL hf
  apply squeeze_zero' ?_ ?_
    (by simpa using (hf.const_mul C).add (hL.const_mul D))
  · exact Filter.Eventually.of_forall fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg)
  rw [eventually_inf_principal]
  filter_upwards with (n, I) hnI
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hx := (hnI.1 i hi).1
  have hy := (hnI.1 i hi).2
  calc
    dist (L (I i).1 (f (I i).1)) (L (I i).2 (f (I i).2)) ≤
        dist (L (I i).1 (f (I i).1)) (L (I i).1 (f (I i).2)) +
        dist (L (I i).1 (f (I i).2)) (L (I i).2 (f (I i).2)) := dist_triangle _ _ _
    _ ≤ ‖L (I i).1‖ * dist (f (I i).1) (f (I i).2) +
        dist (L (I i).1) (L (I i).2) * ‖f (I i).2‖ := by
      simp only [dist_eq_norm]
      apply add_le_add
      · rw [← map_sub]
        exact (L (I i).1).le_opNorm _
      · exact (L (I i).1 - L (I i).2).le_opNorm _
    _ ≤ C * dist (f (I i).1) (f (I i).2) +
        D * dist (L (I i).1) (L (I i).2) := by
      rw [mul_comm D]
      exact add_le_add (mul_le_mul_of_nonneg_right (hC _ hx) dist_nonneg)
        (mul_le_mul_of_nonneg_left (hD _ hy) dist_nonneg)

/-- A continuous operator family on a compact interval acts on integrable profiles. -/
theorem intervalIntegrable_clm_apply {L : ℝ → E →L[ℝ] F} {g : ℝ → E} {a b : ℝ}
    (hL : ContinuousOn L (uIcc a b)) (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t => L t (g t)) volume a b := by
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hL
  rw [intervalIntegrable_iff] at hg ⊢
  have hm := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (hL.intervalIntegrable.aestronglyMeasurable_restrict_uIoc.prodMk hg.aestronglyMeasurable)
  apply (hg.norm.const_mul C).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  exact (L t).le_opNorm (g t) |>.trans
    (mul_le_mul_of_nonneg_right (hC t (uIoc_subset_uIcc ht)) (norm_nonneg _))

variable [CompleteSpace F]

/-- The product rule integrated for Banach-valued profiles and varying bounded functionals. -/
theorem integral_clm_product_rule {L M : ℝ → E →L[ℝ] F} {f g : ℝ → E} {a b : ℝ}
    (hL : AbsolutelyContinuousOnInterval L a b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hLd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt L (M t) t)
    (hfd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt f (g t) t)
    (hi : IntervalIntegrable (fun t => L t (g t) + M t (f t)) volume a b) :
    (∫ t in a..b, L t (g t) + M t (f t)) = L b (f b) - L a (f a) := by
  apply banach_integral_eq_sub_of_ae_hasDerivAt (absolutelyContinuous_clm_apply hL hf) hi
  filter_upwards [hLd, hfd] with t ht hf htI
  simpa only [add_comm] using (ht htI).clm_apply (hf htI)

end KsIndex.Trace
