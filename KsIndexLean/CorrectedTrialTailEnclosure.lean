module

public import KsIndexLean.AlphaQTailEnclosure
public import KsIndexLean.ReciprocalWeightTail
public import KsIndexLean.PowerArcScaledTails

@[expose] public section


/-! # Two-sided reciprocal-corrected trial-tail enclosure

From ratio-endpoint bounds for the 25 coefficient terms, this module proves
summability and upper and lower bounds for a reciprocal-corrected trial tail.
For boundary points `r`, certified centers `v`, radii `e`, and weight offset `c`,
the bounds are

  lower: E − δ − (4/c²)·(E + δ),    upper: E + δ,

where `E = tailCenter r v` and
`δ = tailProductUpper r v e c + tailRadius r v e`.

To apply the enclosure at a window radius R, supply the ratio-endpoint bounds
for the appropriate tail. For example, the positive P tail uses
`r i = 2R+2+shift i` and `c = 6R+7`. The identities
`sample_positive_tail` and `sample_negative_tail` identify the concrete trial
samples with the tail expressions. Both enclosure endpoints use the same ratio
intervals; their rational centers and radii can be evaluated exactly.

Contributed by Claude Fable 5. -/
namespace KsIndex.AlphaRemarkTrial
open PowerArc CertifiedApproximation

/-- Summability of the linear-weight trial tail
`∑ i, tailScale i * g (exponent i) (r i + 2n)` for a real weight offset `c`. -/
theorem trial_tail_linear_summable (r : Fin 25 → ℝ) (c : ℝ) (hr : ∀ i, 1 ≤ r i) :
    Summable (fun n : ℕ =>
      (6*n+c)*(∑ i, tailScale i*g (exponent i) (r i+2*n))^2) := by
  let f := fun (i j : Fin 25) (n : ℕ) =>
    (6*n+c)*(tailScale i*g (exponent i) (r i+2*n))*
      (tailScale j*g (exponent j) (r j+2*n))
  have hf (i j : Fin 25) : Summable (f i j) :=
    scaled_mixed_linear_summable (tailScale i) (tailScale j)
      (exponent_pos i) (exponent_pos j) (hr i) (hr j) (c := c)
  have hs := summable_sum (fun i (_ : i ∈ Finset.univ) =>
    summable_sum (fun j (_ : j ∈ Finset.univ) => hf i j))
  apply hs.congr
  intro n
  simp only [f, pow_two, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- Two-sided reciprocal-corrected enclosure of a trial energy tail, generic in the
boundary data `(r, v, e, c)`. Composes `trial_tail_interval` (the proven generic
C/D/P enclosure) with `corrected_weight_tail_enclosure` (which returns both sides);
`w n = 6n + c ≥ c > 0` supplies the weight floor. -/
theorem corrected_trial_tail_enclosure (r v e : Fin 25 → ℝ) (c : ℝ)
    (hc : 0 < c) (hr : ∀ i, 1 ≤ r i) (he : ∀ i, 0 ≤ e i)
    (hv : ∀ i, |g (exponent i) (r i)/g (exponent i) 0-v i| ≤ e i) :
    Summable (fun n : ℕ => ((6*n+c)-4/(6*n+c))*
        (∑ i, tailScale i*g (exponent i) (r i+2*n))^2) ∧
      tailCenter r v-(tailProductUpper r v e c+tailRadius r v e)-
          (4/c^2)*(tailCenter r v+(tailProductUpper r v e c+tailRadius r v e)) ≤
        (∑' n : ℕ, ((6*n+c)-4/(6*n+c))*
          (∑ i, tailScale i*g (exponent i) (r i+2*n))^2) ∧
      (∑' n : ℕ, ((6*n+c)-4/(6*n+c))*
          (∑ i, tailScale i*g (exponent i) (r i+2*n))^2) ≤
        tailCenter r v+(tailProductUpper r v e c+tailRadius r v e) := by
  have hw : ∀ n : ℕ, c ≤ 6*(n:ℝ)+c := fun n => by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  exact corrected_weight_tail_enclosure
    (fun n : ℕ => (6*(n:ℝ)+c))
    (fun n : ℕ => ∑ i, tailScale i*g (exponent i) (r i+2*n))
    c (tailCenter r v) (tailProductUpper r v e c+tailRadius r v e)
    hc hw (trial_tail_linear_summable r c hr)
    (trial_tail_interval r v e c hr he hv)

end KsIndex.AlphaRemarkTrial

#print axioms KsIndex.AlphaRemarkTrial.trial_tail_linear_summable
#print axioms KsIndex.AlphaRemarkTrial.corrected_trial_tail_enclosure
