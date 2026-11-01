module

public import KsIndexLean.AlphaTrialBudgetAssembly

@[expose] public section


/-! Rational signed enclosures for the actual finite residual window. -/
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual

/-- A rational radius extracted from a signed interval. -/
def signedIntervalRadius (lo hi : ℚ) : ℚ := max |lo| |hi|

lemma signedIntervalRadius_bounds (lo hi : ℚ) (x : ℝ)
    (hl : (lo : ℝ) ≤ x) (hu : x ≤ (hi : ℝ)) :
    |x| ≤ (signedIntervalRadius lo hi : ℝ) := by
  have h1 : -(signedIntervalRadius lo hi : ℝ) ≤ (lo : ℝ) := by
    exact_mod_cast (show -max |lo| |hi| ≤ lo from
      (neg_le_neg (le_max_left _ _)).trans (neg_abs_le lo))
  have h2 : (hi : ℝ) ≤ (signedIntervalRadius lo hi : ℝ) := by
    exact_mod_cast ((le_abs_self hi).trans (le_max_right |lo| |hi|))
  exact abs_le.mpr ⟨h1.trans hl, hu.trans h2⟩

/-- A rational upper-energy table is sound for signed enclosures of actual residuals. -/
theorem signed_window_energy_bound (p : Finset ℤ) (lo hi : ℤ → ℚ)
    (e : ℤ → ℚ) (B : ℚ)
    (hencloses : ∀ n ∈ p,
      (lo n : ℝ) ≤ realResidual AlphaRemark.spectralUpper n ∧
      realResidual AlphaRemark.spectralUpper n ≤ (hi n : ℝ))
    (hrow : ∀ n ∈ p,
      (signedIntervalRadius (lo n) (hi n) : ℝ)^2 / residualWeight n ≤ (e n : ℝ))
    (hsum : ∑ n ∈ p, e n ≤ B) :
    ∑ n ∈ p, realResidual AlphaRemark.spectralUpper n ^ 2 / residualWeight n ≤ (B : ℝ) := by
  have hh : ∀ n ∈ p,
      realResidual AlphaRemark.spectralUpper n ^ 2 / residualWeight n ≤ (e n : ℝ) := by
    intro n hn
    have hb := signedIntervalRadius_bounds (lo n) (hi n) _
      (hencloses n hn).1 (hencloses n hn).2
    have h0 : (0 : ℝ) ≤ signedIntervalRadius (lo n) (hi n) := (abs_nonneg _).trans hb
    have hs := (sq_le_sq₀ (abs_nonneg _) h0).mpr hb
    rw [sq_abs] at hs
    exact (div_le_div_of_nonneg_right hs (residualWeight_pos n).le).trans (hrow n hn)
  exact (Finset.sum_le_sum hh).trans (by exact_mod_cast hsum)

/-- The exact rational value of the residual weight. -/
def residualWeightRat (n : ℤ) : ℚ :=
  if n = 0 then 1 else ((6*(n : ℚ)+1)^2-4)/|6*(n : ℚ)+1|

@[simp] theorem residualWeightRat_cast (n : ℤ) :
    (residualWeightRat n : ℝ) = residualWeight n := by
  by_cases hn : n = 0 <;> simp [residualWeightRat, residualWeight, sigP, hn]

/-- All arithmetic obligations after actual signed enclosure are rational. -/
theorem signed_window_rational_bound (p : Finset ℤ) (lo hi e : ℤ → ℚ) (B : ℚ)
    (hencloses : ∀ n ∈ p,
      (lo n : ℝ) ≤ realResidual AlphaRemark.spectralUpper n ∧
      realResidual AlphaRemark.spectralUpper n ≤ (hi n : ℝ))
    (hrow : ∀ n ∈ p,
      signedIntervalRadius (lo n) (hi n)^2 / residualWeightRat n ≤ e n)
    (hsum : ∑ n ∈ p, e n ≤ B) :
    ∑ n ∈ p, realResidual AlphaRemark.spectralUpper n ^ 2 / residualWeight n ≤ (B : ℝ) := by
  apply signed_window_energy_bound p lo hi e B hencloses ?_ hsum
  intro n hn
  have h := hrow n hn
  rw [← residualWeightRat_cast]
  exact_mod_cast h

/-- Keep the four direct low modes separate from the recurrence-certified modes. -/
theorem window_energy_split_low (N : ℕ) (hN : 2 ≤ N) (f : ℤ → ℝ) :
    (∑ n ∈ residualWindow N, f n) =
      (∑ n ∈ residualWindow 2, f n) +
      ∑ n ∈ residualWindow N \ residualWindow 2, f n := by
  have hsub : residualWindow 2 ⊆ residualWindow N := by
    intro n hn
    simp only [mem_residualWindow] at hn ⊢
    exact ⟨hn.1, hn.2.trans (by exact_mod_cast hN)⟩
  simpa only [add_comm] using (Finset.sum_sdiff (f := f) hsub).symm

/-- The middle range excludes exactly the four direct low modes and the zero head. -/
theorem mem_middleWindow (N : ℕ) (n : ℤ) :
    n ∈ residualWindow N \ residualWindow 2 ↔ 3 ≤ |n| ∧ |n| ≤ (N : ℤ) := by
  simp only [Finset.mem_sdiff, mem_residualWindow]
  have h := abs_nonneg n
  have hz : |n| = 0 ↔ n = 0 := abs_eq_zero
  omega

/-- Concrete allocation for the four direct modes and recurrence window. -/
theorem actual_window1025_of_low_middle
    (hlow : (∑ n ∈ residualWindow 2,
      realResidual AlphaRemark.spectralUpper n ^ 2 / residualWeight n) ≤ (1/10000000 : ℝ))
    (hmiddle : (∑ n ∈ residualWindow 1025 \ residualWindow 2,
      realResidual AlphaRemark.spectralUpper n ^ 2 / residualWeight n) ≤ (6/10000000 : ℝ)) :
    (∑ n ∈ residualWindow 1025,
      realResidual AlphaRemark.spectralUpper n ^ 2 / residualWeight n) ≤ (7/10000000 : ℝ) := by
  rw [window_energy_split_low 1025 (by norm_num)]
  linarith

end KsIndex.AlphaRemarkTrial
