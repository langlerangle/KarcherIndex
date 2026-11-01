module

public import KsIndexLean.NegSignTailIntervals
public import KsIndexLean.AlphaTrialIntegerData

@[expose] public section


/-! Rational mirrors of the tail upper bounds: the generator supplies exact ℚ
centers and radii, the bounds are evaluated in ℚ, and single cast lemmas carry
them to the real statements. No numerical sign is asserted. -/

noncomputable section
namespace KsIndex.AlphaRemarkTrial
open PowerArc

/-! ### ℚ data for the trial, with cast lemmas. -/

def exponentQ (i : Fin 25) : ℚ :=
  if i.val < 12 then 4323618 / 10000000 else 5676382 / 10000000

lemma exponentQ_cast (i : Fin 25) : ((exponentQ i : ℚ) : ℝ) = exponent i := by
  fin_cases i <;> norm_num [exponentQ, exponent]

lemma exponentQ_pos (i : Fin 25) : 0 < exponentQ i := by
  unfold exponentQ
  split_ifs <;> norm_num

def coefficientQ (i : Fin 25) : ℚ := (coefficientNumerator i : ℚ) / 10 ^ 12

lemma coefficientQ_cast (i : Fin 25) :
    ((coefficientQ i : ℚ) : ℝ) = (coefficient i).re := by
  rw [coefficient_re_eq, coefficientQ]
  push_cast
  norm_num

def pairWeightQ (i j : Fin 25) : ℚ :=
  3 * coefficientQ i * coefficientQ j / (2 * (exponentQ i + exponentQ j))

lemma pairWeightQ_cast (i j : Fin 25) :
    ((pairWeightQ i j : ℚ) : ℝ) = pairWeight i j := by
  rw [pairWeightQ, pairWeight]
  push_cast [exponentQ_cast, coefficientQ_cast]
  ring

/-! ### ℚ upper bounds for the two tail quantities. -/

def tailLeadingUpperQ (cen rad : Fin 25 → ℚ) : ℚ :=
  ∑ i, ∑ j, (pairWeightQ i j * (cen i * cen j)
    + |pairWeightQ i j| * (|cen i| * rad j + |cen j| * rad i + rad i * rad j))

def tailErrorUpperQ (rq : Fin 25 → ℚ) (c : ℚ) (cen rad : Fin 25 → ℚ) : ℚ :=
  ∑ i, ∑ j,
    |c - 3 * (exponentQ j * rq i + exponentQ i * rq j) / (exponentQ i + exponentQ j)| *
      ((coefficientQ i ^ 2 * (|cen i| + rad i) ^ 2 / (4 * exponentQ i * rq i)
        + coefficientQ j ^ 2 * (|cen j| + rad j) ^ 2 / (4 * exponentQ j * rq j)) / 2)

/-- The leading tail is at most the cast of its ℚ bound. -/
theorem tailLeading_le_Q (r : Fin 25 → ℝ) (cen rad : Fin 25 → ℚ)
    (hrad : ∀ i, 0 ≤ rad i)
    (he : ∀ i, |tailEndpoint r i - ((cen i : ℚ) : ℝ)| ≤ ((rad i : ℚ) : ℝ)) :
    tailLeading r ≤ ((tailLeadingUpperQ cen rad : ℚ) : ℝ) := by
  have h := tailLeading_le_of_intervals r (fun i => ((cen i : ℚ) : ℝ))
    (fun i => ((rad i : ℚ) : ℝ))
    (fun i => by exact_mod_cast hrad i) he
  apply h.trans_eq
  rw [tailLeadingUpperQ]
  push_cast [pairWeightQ_cast]
  rfl

/-- The error tail is at most the cast of its ℚ bound, at integer-valued starts. -/
theorem tailError_le_Q (r : Fin 25 → ℝ) (rq : Fin 25 → ℚ) (c : ℚ)
    (cen rad : Fin 25 → ℚ)
    (hr : ∀ i, r i = ((rq i : ℚ) : ℝ)) (hr1 : ∀ i, 1 ≤ rq i)
    (hrad : ∀ i, 0 ≤ rad i)
    (he : ∀ i, |tailEndpoint r i - ((cen i : ℚ) : ℝ)| ≤ ((rad i : ℚ) : ℝ)) :
    tailError r ((c : ℚ) : ℝ) ≤ ((tailErrorUpperQ rq c cen rad : ℚ) : ℝ) := by
  have h := tailError_le_of_intervals r ((c : ℚ) : ℝ) (fun i => ((cen i : ℚ) : ℝ))
    (fun i => ((rad i : ℚ) : ℝ))
    (fun i => by rw [hr i]; exact_mod_cast hr1 i)
    (fun i => by exact_mod_cast hrad i) he
  apply h.trans_eq
  rw [tailErrorUpperQ]
  push_cast [exponentQ_cast, coefficientQ_cast]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hr i, hr j]

end KsIndex.AlphaRemarkTrial
