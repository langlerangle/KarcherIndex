module

public import KsIndexLean.CircleSigmaDomain

@[expose] public section


/-! Comparison with the paper's half-order squared-norm weight `sqrt(1+n²)`.
The repository's equivalent half-order weight is `1+|n|`. -/
noncomputable section
namespace KsIndex.CircleSobolev

lemma paperHalfWeight_le (x : ℝ) : Real.sqrt (1 + x ^ 2) ≤ 1 + |x| := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  nlinarith [Real.sqrt_nonneg (1 + x ^ 2), abs_nonneg x, sq_abs x]

lemma halfWeight_le_twice_paper (x : ℝ) :
    1 + |x| ≤ 2 * Real.sqrt (1 + x ^ 2) := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + x ^ 2 by positivity)
  have h1 : 1 ≤ Real.sqrt (1 + x ^ 2) := by
    nlinarith [Real.sqrt_nonneg (1 + x ^ 2), sq_nonneg x]
  have ha : |x| ≤ Real.sqrt (1 + x ^ 2) := by
    nlinarith [Real.sqrt_nonneg (1 + x ^ 2), abs_nonneg x, sq_abs x]
  linarith

/-- The two half-order weights define exactly the same coefficient domain. -/
theorem summable_paperHalf_iff (a : ℤ → ℂ) :
    Summable (fun n : ℤ => Real.sqrt (1 + (n : ℝ) ^ 2) * ‖a n‖ ^ 2) ↔
      Summable (fun n : ℤ => (1 + |(n : ℝ)|) * ‖a n‖ ^ 2) := by
  constructor
  · intro h
    apply (h.mul_left 2).of_nonneg_of_le (fun n => by positivity)
    intro n
    nlinarith [halfWeight_le_twice_paper (n : ℝ), sq_nonneg ‖a n‖]
  · intro h
    apply h.of_nonneg_of_le (fun n => by positivity)
    intro n
    exact mul_le_mul_of_nonneg_right (paperHalfWeight_le (n : ℝ)) (sq_nonneg _)

/-- The paper's half-order squared norm, evaluated on the same physical coefficients. -/
def paperHalfNormSq (u : Space (1 / 2 : ℝ)) : ℝ :=
  ∑' n : ℤ, Real.sqrt (1 + (n : ℝ) ^ 2) * ‖coeff (1 / 2 : ℝ) u n‖ ^ 2

lemma summable_paperHalfNormSq (u : Space (1 / 2 : ℝ)) :
    Summable (fun n : ℤ => Real.sqrt (1 + (n : ℝ) ^ 2) *
      ‖coeff (1 / 2 : ℝ) u n‖ ^ 2) := by
  apply (summable_paperHalf_iff _).mpr
  simpa only [weight_sq, show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
    using (hasSum_weighted_sq (1 / 2 : ℝ) u).summable

/-- The paper norm is no larger than the repository norm. -/
theorem paperHalfNormSq_le (u : Space (1 / 2 : ℝ)) : paperHalfNormSq u ≤ ‖u‖ ^ 2 := by
  have hm := hasSum_weighted_sq (1 / 2 : ℝ) u
  simp only [weight_sq, show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at hm
  rw [← hm.tsum_eq]
  exact (summable_paperHalfNormSq u).tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right (paperHalfWeight_le (n : ℝ)) (sq_nonneg _))
    hm.summable

/-- Conversely, the repository squared norm is at most twice the paper's. -/
theorem norm_sq_le_twice_paperHalfNormSq (u : Space (1 / 2 : ℝ)) :
    ‖u‖ ^ 2 ≤ 2 * paperHalfNormSq u := by
  have hm := hasSum_weighted_sq (1 / 2 : ℝ) u
  simp only [weight_sq, show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] at hm
  have h := hm.summable.tsum_le_tsum (fun (n : ℤ) =>
    show (1 + |(n : ℝ)|) * ‖coeff (1 / 2 : ℝ) u n‖ ^ 2 ≤
      2 * (Real.sqrt (1 + (n : ℝ) ^ 2) * ‖coeff (1 / 2 : ℝ) u n‖ ^ 2) by
      nlinarith [halfWeight_le_twice_paper (n : ℝ),
        sq_nonneg ‖coeff (1 / 2 : ℝ) u n‖]) ((summable_paperHalfNormSq u).mul_left 2)
  simpa only [hm.tsum_eq, tsum_mul_left, paperHalfNormSq] using h

/-- The paper's squared graph norm, using its two half-order Fourier sums. -/
def paperGraphNormSq (q : ↥sigmaGraph) : ℝ :=
  paperHalfNormSq (q : SigmaGraphAmbient).fst + paperHalfNormSq (q : SigmaGraphAmbient).snd

theorem paperGraphNormSq_le (q : ↥sigmaGraph) : paperGraphNormSq q ≤ ‖q‖ ^ 2 := by
  rw [sigmaGraph_norm_sq]
  exact add_le_add (paperHalfNormSq_le _) (paperHalfNormSq_le _)

theorem norm_sq_le_twice_paperGraphNormSq (q : ↥sigmaGraph) :
    ‖q‖ ^ 2 ≤ 2 * paperGraphNormSq q := by
  rw [sigmaGraph_norm_sq]
  have h1 := norm_sq_le_twice_paperHalfNormSq (q : SigmaGraphAmbient).fst
  have h2 := norm_sq_le_twice_paperHalfNormSq (q : SigmaGraphAmbient).snd
  unfold paperGraphNormSq
  linarith

end KsIndex.CircleSobolev
