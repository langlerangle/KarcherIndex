module

public import KsIndexLean.AlphaTrialSampleCertificate
public import KsIndexLean.PowerArcFiniteTailEnergy

@[expose] public section


/-! Two-sided tail energy bounds for the concrete normalized trial. -/

namespace KsIndex.AlphaRemarkTrial
open PowerArc

noncomputable def tailScale (i : Fin 25) : ℝ := (coefficient i).re / g (exponent i) 0

noncomputable def tailLeading (r : Fin 25 → ℝ) : ℝ :=
  ∑ i, ∑ j, 3 * (tailScale i * tailScale j * mixedPrimitive (exponent i) (exponent j) (r i) (r j))

noncomputable def tailError (r : Fin 25 → ℝ) (c : ℝ) : ℝ :=
  ∑ i, ∑ j, |c - 3 * (exponent j * r i + exponent i * r j) / (exponent i + exponent j)| *
    ((tailScale i ^ 2 * (energyPrimitive (exponent i) (r i) / r i) +
      tailScale j ^ 2 * (energyPrimitive (exponent j) (r j) / r j)) / 2)

/-- Express the leading term using normalized endpoint samples and the starting
parameters `r`. The identity holds for arbitrary real starting parameters. -/
lemma tailLeading_eq (r : Fin 25 → ℝ) :
    tailLeading r = ∑ i, ∑ j, 3 * (coefficient i).re * (coefficient j).re *
      (((r i + exponent i) * (g (exponent i) (r i) / g (exponent i) 0)) *
       ((r j + exponent j) * (g (exponent j) (r j) / g (exponent j) 0)) /
        (2 * (exponent i + exponent j))) := by
  unfold tailLeading tailScale mixedPrimitive
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [div_eq_mul_inv]
  ring

lemma tailError_eq (r : Fin 25 → ℝ) (c : ℝ) :
    tailError r c = ∑ i, ∑ j,
      |c - 3 * (exponent j * r i + exponent i * r j) / (exponent i + exponent j)| *
      (((coefficient i).re ^ 2 * ((r i + exponent i) *
          (g (exponent i) (r i) / g (exponent i) 0)) ^ 2 / (4 * exponent i * r i) +
        (coefficient j).re ^ 2 * ((r j + exponent j) *
          (g (exponent j) (r j) / g (exponent j) 0)) ^ 2 / (4 * exponent j * r j)) / 2) := by
  unfold tailError tailScale energyPrimitive
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma shift_bounds (i : Fin 25) : (-6 : ℤ) ≤ shift i ∧ shift i ≤ 6 := by
  fin_cases i <;> norm_num [shift]

lemma sample_positive_tail (K : ℤ) (n : ℕ) :
    sample (K + 2 * n) = ∑ i, tailScale i * g (exponent i) ((K + shift i : ℤ) + 2 * (n : ℝ)) := by
  unfold sample tailScale
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  rw [show (K : ℝ) + 2 * n + shift i = K + shift i + 2 * n by ring]
  ring

lemma sample_negative_tail (K : ℤ) (n : ℕ) :
    sample (-K - 2 * n) = ∑ i, tailScale i * g (exponent i) ((K - shift i : ℤ) + 2 * (n : ℝ)) := by
  unfold sample tailScale
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  rw [show -(K : ℝ) - 2 * n + shift i = -(K - shift i + 2 * n) by ring, g_neg]
  ring

/-- Positive-frequency tail, with an explicit starting sample and linear weight. -/
theorem positive_sample_tail_bound (K : ℤ) (hK : 7 ≤ K) (c : ℝ) :
    |(∑' n : ℕ, (6 * n + c) * sample (K + 2 * n) ^ 2) -
      tailLeading (fun i => (K + shift i : ℤ))| ≤
      tailError (fun i => (K + shift i : ℤ)) c := by
  have hr : ∀ i, (1 : ℝ) ≤ (K + shift i : ℤ) := by
    intro i
    have hi := (shift_bounds i).1
    exact_mod_cast (show (1 : ℤ) ≤ K + shift i by omega)
  simpa only [sample_positive_tail, tailLeading, tailError] using
    finite_linear_tail_energy_bound exponent (fun i => (K + shift i : ℤ))
      tailScale c exponent_pos hr

/-- Negative-frequency tail uses evenness of g, reversing every shift. -/
theorem negative_sample_tail_bound (K : ℤ) (hK : 7 ≤ K) (c : ℝ) :
    |(∑' n : ℕ, (6 * n + c) * sample (-K - 2 * n) ^ 2) -
      tailLeading (fun i => (K - shift i : ℤ))| ≤
      tailError (fun i => (K - shift i : ℤ)) c := by
  have hr : ∀ i, (1 : ℝ) ≤ (K - shift i : ℤ) := by
    intro i
    have hi := (shift_bounds i).2
    exact_mod_cast (show (1 : ℤ) ≤ K - shift i by omega)
  simpa only [sample_negative_tail, tailLeading, tailError] using
    finite_linear_tail_energy_bound exponent (fun i => (K - shift i : ℤ))
      tailScale c exponent_pos hr

end KsIndex.AlphaRemarkTrial
