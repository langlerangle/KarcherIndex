module

public import Mathlib

@[expose] public section


/-! Recovering a reciprocal-corrected energy tail from a positive-weight tail. -/
namespace KsIndex

theorem reciprocal_weight_tail_bound {ι : Type*} (w f : ι → ℝ) (c : ℝ)
    (hc : 0 < c) (hw : ∀ i, c ≤ w i)
    (hs : Summable (fun i => w i * f i ^ 2)) :
    Summable (fun i => 4 / w i * f i ^ 2) ∧
      0 ≤ (∑' i, 4 / w i * f i ^ 2) ∧
      (∑' i, 4 / w i * f i ^ 2) ≤ (4 / c ^ 2) * (∑' i, w i * f i ^ 2) := by
  have hp (i : ι) : 0 < w i := lt_of_lt_of_le hc (hw i)
  have hm (i : ι) : 4 / w i * f i ^ 2 ≤ (4 / c ^ 2) * (w i * f i ^ 2) := by
    have hsq : c^2 ≤ (w i)^2 := by nlinarith [hw i]
    have hdiv : 4 / w i ≤ (4 / c^2) * w i := by
      apply (div_le_iff₀ (hp i)).2
      rw [show 4 / c^2 * w i * w i = (4*(w i)^2)/c^2 by ring]
      apply (le_div_iff₀ (sq_pos_of_pos hc)).2
      nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hdiv) (sq_nonneg (f i))]
  have hn (i : ι) : 0 ≤ 4 / w i * f i ^ 2 := by
    exact mul_nonneg (div_nonneg (by norm_num) (hp i).le) (sq_nonneg _)
  have ht := (hs.mul_left (4/c^2)).of_nonneg_of_le hn hm
  refine ⟨ht, tsum_nonneg hn, ?_⟩
  simpa only [tsum_mul_left] using ht.tsum_le_tsum hm (hs.mul_left (4/c^2))

/-- An enclosure of the linear energy gives a lower bound for the full symbol. -/
theorem corrected_weight_tail_enclosure {ι : Type*} (w f : ι → ℝ)
    (c E δ : ℝ) (hc : 0 < c) (hw : ∀ i, c ≤ w i)
    (hs : Summable (fun i => w i*f i^2))
    (he : |(∑' i, w i*f i^2)-E| ≤ δ) :
    Summable (fun i => (w i-4/w i)*f i^2) ∧
      E-δ-(4/c^2)*(E+δ) ≤ (∑' i, (w i-4/w i)*f i^2) ∧
      (∑' i, (w i-4/w i)*f i^2) ≤ E+δ := by
  obtain ⟨hr, hr0, hrle⟩ := reciprocal_weight_tail_bound w f c hc hw hs
  have hfun : (fun i => (w i-4/w i)*f i^2) =
      (fun i => w i*f i^2 - 4/w i*f i^2) := by funext i; ring
  rw [hfun]
  refine ⟨hs.sub hr, ?_⟩
  rw [hs.tsum_sub hr]
  have hlow := (abs_le.mp he).1
  have hupp := (abs_le.mp he).2
  have hb : (∑' i, 4/w i*f i^2) ≤ (4/c^2)*(E+δ) :=
    hrle.trans (mul_le_mul_of_nonneg_left (by linarith : (∑' i, w i*f i^2) ≤ E+δ)
      (by positivity))
  constructor <;> linarith

end KsIndex
