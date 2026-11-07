module

public import KsIndexLean.AlphaQTailEnclosure
public import KsIndexLean.ReciprocalWeightTail
public import KsIndexLean.PowerArcScaledTails

@[expose] public section


/-! # Generic two-sided reciprocal-corrected trial-tail enclosure

DRAFT (Xi, 2026-11-06, per Astra 4130) — SOURCE-ONLY, NOT YET COMPILED.

Abstracts the per-cutoff tail pattern of `AlphaEnergy8192PplusCertificate` into a single
generic lemma: from the 25 ratio-endpoint hypotheses alone (boundary points `r`,
certified centers `v`, radii `e`, weight offset `c`), it yields summability of the
reciprocal-corrected tail together with BOTH bounds returned by
`corrected_weight_tail_enclosure`:

  lower  E − δ − (4/c²)·(E + δ)   and   upper  E + δ,

where `E = tailCenter r v` and `δ = tailProductUpper r v e c + tailRadius r v e`.

Instantiation at a cutoff R (per the four families' boundary maps, e.g. Pplus:
`r i = 2R+2+shift i`, `c = 6R+7`) is then: supply the 25 ratio-endpoint certificates
(Astra 4128's generated form), rewrite the concrete `sample` via
`sample_positive_tail` / `sample_negative_tail` exactly as the 8192 certificates do,
and evaluate `tailCenter/tailRadius/tailProductUpper` at exact rational literals —
no coarse intermediate rounding (per the 4125/4127 exact-literal requirement).
No scaled-endpoint duplication: both sides come from ratio intervals (Astra 4130). -/
namespace KsIndex.AlphaRemarkTrial
open PowerArc CertifiedApproximation

/-- Generic summability of the linear-weight trial tail: `linear_tail_summable` of the
8192 Pplus certificate, generalized from the literal weight offset to any `c : ℝ`
(`scaled_mixed_linear_summable` is already generic in `c`) and stated directly on the
`∑ i, tailScale i * g (exponent i) (r i + 2n)` shape, before any `sample` rewriting. -/
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
