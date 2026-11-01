module

public import KsIndexLean.StieltjesFiniteRounding

@[expose] public section


/-! A single-pass integer evaluator for rounded Stieltjes sums.

The state retains the next coefficient and the accumulated weighted sum.
Theorems identify both outputs with their mathematical definitions, so a
checked state value supplies a finite analytic enclosure.
-/

namespace KsIndex.PowerArc

def roundedStieltjesState (B D r S Znum Zden : ℤ) : ℕ → ℤ × ℤ
  | 0 => (S, 0)
  | n + 1 =>
    let p := roundedStieltjesState B D r S Znum Zden n
    ((B - D * (r + 2 * n)) * p.1 / (B + D * (r + 2 * n + 2)),
      p.2 + (((-1 : ℤ) ^ n * Zden) * p.1) / ((n : ℤ) * Zden + Znum))

theorem roundedStieltjesState_fst (B D r S Znum Zden : ℤ) (N : ℕ) :
    (roundedStieltjesState B D r S Znum Zden N).1 = roundedCoefficient B D r S N := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [roundedStieltjesState, roundedCoefficient, ih]

theorem roundedStieltjesState_snd (B D r S Znum Zden : ℤ) (N : ℕ) :
    (roundedStieltjesState B D r S Znum Zden N).2 =
      ∑ k ∈ Finset.range N, roundedStieltjesTerm (roundedCoefficient B D r S) Znum Zden k := by
  induction N with
  | zero => simp [roundedStieltjesState]
  | succ N ih =>
    simp only [roundedStieltjesState, Finset.sum_range_succ, ih,
      roundedStieltjesState_fst, roundedStieltjesTerm]

/-- Evaluate a bounded block starting from a previously checked state. -/
def roundedStieltjesBlock (B D r Znum Zden : ℤ) (start : ℕ) (initial : ℤ × ℤ) :
    ℕ → ℤ × ℤ
  | 0 => initial
  | n + 1 =>
    let p := roundedStieltjesBlock B D r Znum Zden start initial n
    let k := start + n
    ((B - D * (r + 2 * k)) * p.1 / (B + D * (r + 2 * k + 2)),
      p.2 + (((-1 : ℤ) ^ (k % 2) * Zden) * p.1) / ((k : ℤ) * Zden + Znum))

/-- Checked blocks compose without reevaluating the preceding prefix. -/
theorem roundedStieltjesState_add (B D r S Znum Zden : ℤ) (start len : ℕ) :
    roundedStieltjesState B D r S Znum Zden (start + len) =
      roundedStieltjesBlock B D r Znum Zden start
        (roundedStieltjesState B D r S Znum Zden start) len := by
  induction len with
  | zero => simp [roundedStieltjesBlock]
  | succ len ih =>
    rw [Nat.add_succ, roundedStieltjesState, roundedStieltjesBlock, ih]
    rw [neg_one_pow_eq_pow_mod_two (start + len)]

/-- A verified accumulator value encloses the corresponding finite analytic sum. -/
theorem roundedStieltjesState_error (B D r S Znum Zden : ℤ) (N : ℕ)
    (hB : 0 < B) (hD : 0 < D) (hr : 0 ≤ r) (hS : 0 < S)
    (hnum : 0 < Znum) (hden : 0 < Zden) :
    |(∑ k ∈ Finset.range N, (-1 : ℝ) ^ k *
        normalizedCoefficient ((B : ℝ) / D) r k / ((k : ℝ) + (Znum : ℝ) / Zden)) -
      ((roundedStieltjesState B D r S Znum Zden N).2 : ℝ) / S| ≤
      N * ((N : ℝ) * (1 / (S : ℝ)) / ((Znum : ℝ) / Zden) + 1 / (S : ℝ)) := by
  rw [roundedStieltjesState_snd, Int.cast_sum, Finset.sum_div]
  exact roundedStieltjesSum_error B D r S Znum Zden N hB hD hr hS hnum hden

end KsIndex.PowerArc
