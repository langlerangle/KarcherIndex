module

public import KsIndexLean.CircleSobolev

@[expose] public section


/-! Comparison of homogeneous and inhomogeneous Fourier norms.

The homogeneous sum omits the zero mode. On the subspace with zero constant
coefficient, it is equivalent to the inherited Sobolev norm at every real
order, with squared-norm comparison factor `2^|2s|`. The inhomogeneous weight
here is `(1+|n|)^(2s)`.
-/
noncomputable section
namespace KsIndex.CircleSobolev

/-- Symmetrically comparable positive bases have comparable powers at every real exponent. -/
lemma rpow_comparison {x y q : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≤ 2 * y) (hyx : y ≤ 2 * x) :
    x ^ q ≤ (2 : ℝ) ^ |q| * y ^ q := by
  by_cases hq : 0 ≤ q
  · calc
      x ^ q ≤ (2 * y) ^ q := Real.rpow_le_rpow hx.le hxy hq
      _ = (2 : ℝ) ^ |q| * y ^ q := by
        rw [Real.mul_rpow (by norm_num) hy.le, abs_of_nonneg hq]
  · have hq' : q ≤ 0 := le_of_lt (lt_of_not_ge hq)
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < y / 2)
      (by linarith : y / 2 ≤ x) hq'
    calc
      x ^ q ≤ (y / 2) ^ q := h
      _ = (2 : ℝ) ^ |q| * y ^ q := by
        rw [Real.div_rpow hy.le (by norm_num), abs_of_nonpos hq',
          Real.rpow_neg (by norm_num)]
        ring

lemma abs_int_ge_one {n : ℤ} (hn : n ≠ 0) : (1 : ℝ) ≤ |(n : ℝ)| := by
  have h : (1 : ℤ) ≤ |n| := by have := abs_pos.mpr hn; omega
  exact_mod_cast h

/-- Nonzero Fourier weights compare in either direction, uniformly in the mode. -/
lemma homogeneous_weight_comparison (s : ℝ) {n : ℤ} (hn : n ≠ 0) :
    |(n : ℝ)| ^ (2 * s) ≤ (2 : ℝ) ^ |2 * s| * (1 + |(n : ℝ)|) ^ (2 * s) ∧
    (1 + |(n : ℝ)|) ^ (2 * s) ≤ (2 : ℝ) ^ |2 * s| * |(n : ℝ)| ^ (2 * s) := by
  have ha := abs_int_ge_one hn
  constructor
  · exact rpow_comparison (by linarith) (by positivity) (by linarith) (by linarith)
  · exact rpow_comparison (by positivity) (by linarith) (by linarith) (by linarith)

/-- Squared homogeneous coefficient seminorm. Zero mode is excluded explicitly. -/
def homogeneousSq (s : ℝ) (u : Space s) : ℝ :=
  ∑' n : ℤ, if n = 0 then 0 else |(n : ℝ)| ^ (2 * s) * ‖coeff s u n‖ ^ 2

lemma homogeneous_term_nonneg (s : ℝ) (u : Space s) (n : ℤ) :
    0 ≤ (if n = 0 then 0 else |(n : ℝ)| ^ (2 * s) * ‖coeff s u n‖ ^ 2) := by
  split_ifs <;> positivity

lemma homogeneous_term_le (s : ℝ) (u : Space s) (n : ℤ) :
    (if n = 0 then 0 else |(n : ℝ)| ^ (2 * s) * ‖coeff s u n‖ ^ 2) ≤
      (2 : ℝ) ^ |2 * s| * (weight s n ^ 2 * ‖coeff s u n‖ ^ 2) := by
  split_ifs with hn
  · positivity
  · rw [weight_sq]
    have h := mul_le_mul_of_nonneg_right (homogeneous_weight_comparison s hn).1
      (sq_nonneg ‖coeff s u n‖)
    nlinarith

lemma summable_homogeneous (s : ℝ) (u : Space s) :
    Summable (fun n : ℤ => if n = 0 then 0 else |(n : ℝ)| ^ (2 * s) * ‖coeff s u n‖ ^ 2) :=
  Summable.of_nonneg_of_le (homogeneous_term_nonneg s u) (homogeneous_term_le s u)
    ((hasSum_weighted_sq s u).summable.mul_left _)

theorem homogeneousSq_le (s : ℝ) (u : Space s) :
    homogeneousSq s u ≤ (2 : ℝ) ^ |2 * s| * ‖u‖ ^ 2 := by
  have h := Summable.tsum_le_tsum (homogeneous_term_le s u) (summable_homogeneous s u)
    ((hasSum_weighted_sq s u).summable.mul_left ((2 : ℝ) ^ |2 * s|))
  simpa only [homogeneousSq, tsum_mul_left, (hasSum_weighted_sq s u).tsum_eq] using h

theorem norm_sq_le_homogeneousSq (s : ℝ) (u : dotted s) :
    ‖u‖ ^ 2 ≤ (2 : ℝ) ^ |2 * s| * homogeneousSq s u := by
  have hterm : ∀ n : ℤ, weight s n ^ 2 * ‖coeff s u n‖ ^ 2 ≤
      (2 : ℝ) ^ |2 * s| *
        (if n = 0 then 0 else |(n : ℝ)| ^ (2 * s) * ‖coeff s u n‖ ^ 2) := by
    intro n
    by_cases hn : n = 0
    · subst n
      rw [(mem_dotted s u).mp u.property]
      simp
    · rw [ite_eq_right hn, weight_sq]
      have h := mul_le_mul_of_nonneg_right (homogeneous_weight_comparison s hn).2
        (sq_nonneg ‖coeff s u n‖)
      nlinarith
  have h := Summable.tsum_le_tsum hterm (hasSum_weighted_sq s u).summable
    ((summable_homogeneous s u).mul_left ((2 : ℝ) ^ |2 * s|))
  change ‖(u : Space s)‖ ^ 2 ≤ _
  simpa only [(hasSum_weighted_sq s u).tsum_eq, tsum_mul_left, homogeneousSq] using h

/-- The homogeneous Fourier seminorm, defined on the entire Sobolev space.
It is nondegenerate on the subspace with zero constant coefficient. -/
def homogeneousNorm (s : ℝ) (u : Space s) : ℝ := Real.sqrt (homogeneousSq s u)

theorem homogeneousNorm_le (s : ℝ) (u : Space s) :
    homogeneousNorm s u ≤ Real.sqrt ((2 : ℝ) ^ |2 * s|) * ‖u‖ := by
  have h := Real.sqrt_le_sqrt (homogeneousSq_le s u)
  simpa only [homogeneousNorm, Real.sqrt_mul (show 0 ≤ (2 : ℝ) ^ |2 * s| by positivity),
    Real.sqrt_sq (norm_nonneg u)] using h

theorem norm_le_homogeneousNorm (s : ℝ) (u : dotted s) :
    ‖u‖ ≤ Real.sqrt ((2 : ℝ) ^ |2 * s|) * homogeneousNorm s u := by
  have h := Real.sqrt_le_sqrt (norm_sq_le_homogeneousSq s u)
  simpa only [Real.sqrt_sq (norm_nonneg u),
    Real.sqrt_mul (show 0 ≤ (2 : ℝ) ^ |2 * s| by positivity), homogeneousNorm] using h

/-- No extra null directions remain after imposing mean zero. -/
theorem homogeneousNorm_eq_zero_iff (s : ℝ) (u : dotted s) :
    homogeneousNorm s u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hb := norm_le_homogeneousNorm s u
    rw [h, mul_zero] at hb
    exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg u))
  · rintro rfl
    simp [homogeneousNorm, homogeneousSq, coeff]

end KsIndex.CircleSobolev
