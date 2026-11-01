module

public import KsIndexLean.NegSignDecomposition

@[expose] public section


/-! Rational-ready enclosures for the four tail quantities. The only
transcendental inputs are the per-family endpoint samples, which enter through
the gated certified integer-sample intervals; every other factor is rational
data. No numerical sign is asserted. -/

noncomputable section
namespace KsIndex.AlphaRemarkTrial
open PowerArc CertifiedApproximation

/-- The single transcendental input of a tail term: `(r+β)·g(β,r)/g(β,0)`. -/
def tailEndpoint (r : Fin 25 → ℝ) (i : Fin 25) : ℝ :=
  (r i + exponent i) * (g (exponent i) (r i) / g (exponent i) 0)

/-- Certified interval for a tail endpoint, from the gated integer-sample data
at the (shared-stream) frequency `k i`. -/
lemma tailEndpoint_interval {r : Fin 25 → ℝ} {k : Fin 25 → ℤ}
    (hk : ∀ i, r i = ((k i : ℤ) : ℝ)) (hk1 : ∀ i, 1 ≤ k i) (i : Fin 25) :
    |tailEndpoint r i -
      (((k i : ℤ) : ℝ) + exponent i) *
        integerSampleCenter (numerator i) 5000000 (10 ^ 30) (seedCenter i) (k i)| ≤
      (((k i : ℤ) : ℝ) + exponent i) *
        integerSampleError (numerator i) 5000000 (10 ^ 30) (seedCenter i)
          (seedError i) (k i) := by
  have hk1' : (1 : ℝ) ≤ ((k i : ℤ) : ℝ) := by exact_mod_cast hk1 i
  have hpos : 0 ≤ ((k i : ℤ) : ℝ) + exponent i := by
    have := exponent_pos i
    linarith
  have hb := integerSample_bound (numerator_pos i)
    (by norm_num : (0 : ℤ) < 5000000) (by norm_num : (0 : ℤ) < 10 ^ 30)
    (seed_error i) (k i)
  have hexp : (numerator i : ℝ) / ((5000000 : ℤ) : ℝ) = exponent i := by
    rw [exponent_eq]
    norm_num
  rw [hexp] at hb
  have hm := mul_le_mul_of_nonneg_left hb hpos
  rw [← abs_of_nonneg hpos, ← abs_mul, mul_sub] at hm
  rw [abs_of_nonneg hpos] at hm
  rw [tailEndpoint, hk i]
  exact hm

/-- The rational pair weight of a leading-tail term. -/
def pairWeight (i j : Fin 25) : ℝ :=
  3 * (coefficient i).re * (coefficient j).re / (2 * (exponent i + exponent j))

/-- Upper bound for the leading tail from endpoint intervals: centers carry the
signed value, radii enter through absolute values only. -/
lemma tailLeading_le_of_intervals (r : Fin 25 → ℝ) (cen rad : Fin 25 → ℝ)
    (hrad : ∀ i, 0 ≤ rad i)
    (he : ∀ i, |tailEndpoint r i - cen i| ≤ rad i) :
    tailLeading r ≤ ∑ i, ∑ j,
      (pairWeight i j * (cen i * cen j)
        + |pairWeight i j| *
          (|cen i| * rad j + |cen j| * rad i + rad i * rad j)) := by
  rw [tailLeading_eq]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hprod := product_error (hrad i) (he i) (he j)
  have hterm : 3 * (coefficient i).re * (coefficient j).re *
      (tailEndpoint r i * tailEndpoint r j / (2 * (exponent i + exponent j))) =
      pairWeight i j * (tailEndpoint r i * tailEndpoint r j) := by
    rw [pairWeight]
    ring
  have hsplit : pairWeight i j * (tailEndpoint r i * tailEndpoint r j) =
      pairWeight i j * (cen i * cen j)
        + pairWeight i j * (tailEndpoint r i * tailEndpoint r j - cen i * cen j) := by
    ring
  have habs : pairWeight i j *
      (tailEndpoint r i * tailEndpoint r j - cen i * cen j) ≤
      |pairWeight i j| * (|cen i| * rad j + |cen j| * rad i + rad i * rad j) := by
    calc pairWeight i j * (tailEndpoint r i * tailEndpoint r j - cen i * cen j)
        ≤ |pairWeight i j * (tailEndpoint r i * tailEndpoint r j - cen i * cen j)| :=
          le_abs_self _
      _ = |pairWeight i j| * |tailEndpoint r i * tailEndpoint r j - cen i * cen j| :=
          abs_mul _ _
      _ ≤ |pairWeight i j| * (|cen i| * rad j + |cen j| * rad i + rad i * rad j) :=
          mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
  calc 3 * (coefficient i).re * (coefficient j).re *
      (tailEndpoint r i * tailEndpoint r j / (2 * (exponent i + exponent j)))
      = pairWeight i j * (cen i * cen j)
        + pairWeight i j * (tailEndpoint r i * tailEndpoint r j - cen i * cen j) := by
        rw [hterm, hsplit]
    _ ≤ _ := by linarith

/-- Upper bound for the error tail from endpoint intervals. -/
lemma tailError_le_of_intervals (r : Fin 25 → ℝ) (c : ℝ) (cen rad : Fin 25 → ℝ)
    (hr1 : ∀ i, 1 ≤ r i) (_hrad : ∀ i, 0 ≤ rad i)
    (he : ∀ i, |tailEndpoint r i - cen i| ≤ rad i) :
    tailError r c ≤ ∑ i, ∑ j,
      |c - 3 * (exponent j * r i + exponent i * r j) / (exponent i + exponent j)| *
        (((coefficient i).re ^ 2 * (|cen i| + rad i) ^ 2 /
            (4 * exponent i * r i)
          + (coefficient j).re ^ 2 * (|cen j| + rad j) ^ 2 /
            (4 * exponent j * r j)) / 2) := by
  have hsq : ∀ l, tailEndpoint r l ^ 2 ≤ (|cen l| + rad l) ^ 2 := by
    intro l
    have h1 : |tailEndpoint r l| ≤ |cen l| + rad l := by
      have h2 := abs_sub_abs_le_abs_sub (tailEndpoint r l) (cen l)
      linarith [he l]
    calc tailEndpoint r l ^ 2 = |tailEndpoint r l| ^ 2 := (sq_abs _).symm
      _ ≤ (|cen l| + rad l) ^ 2 := by
          nlinarith [abs_nonneg (tailEndpoint r l)]
  have hden : ∀ l, 0 < 4 * exponent l * r l := by
    intro l
    have := exponent_pos l
    have := hr1 l
    positivity
  rw [tailError_eq]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hi : (coefficient i).re ^ 2 *
      ((r i + exponent i) * (g (exponent i) (r i) / g (exponent i) 0)) ^ 2 /
        (4 * exponent i * r i) ≤
      (coefficient i).re ^ 2 * (|cen i| + rad i) ^ 2 / (4 * exponent i * r i) := by
    apply div_le_div_of_nonneg_right _ (hden i).le
    exact mul_le_mul_of_nonneg_left (hsq i) (sq_nonneg _)
  have hj : (coefficient j).re ^ 2 *
      ((r j + exponent j) * (g (exponent j) (r j) / g (exponent j) 0)) ^ 2 /
        (4 * exponent j * r j) ≤
      (coefficient j).re ^ 2 * (|cen j| + rad j) ^ 2 / (4 * exponent j * r j) := by
    apply div_le_div_of_nonneg_right _ (hden j).le
    exact mul_le_mul_of_nonneg_left (hsq j) (sq_nonneg _)
  linarith [hi, hj]

end KsIndex.AlphaRemarkTrial
