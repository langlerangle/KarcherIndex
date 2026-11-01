module

public import KsIndexLean.AlphaTrialWindowCertificate

@[expose] public section


/-! Combining a finite residual window with its complementary tail. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual

/-- Summability of the complement suffices to split a series at a finite set. -/
theorem finite_complement_sum (f : ℤ → ℝ) (p : Finset ℤ)
    (ht : Summable (fun n => if n ∈ p then 0 else f n)) :
    Summable f ∧ (∑' n, f n) = (∑ n ∈ p, f n) +
      ∑' n, (if n ∈ p then 0 else f n) := by
  classical
  have hw : Summable (fun n => if n ∈ p then f n else 0) :=
    summable_of_ne_finset_zero (s := p) (by intro n hn; simp [hn])
  have he : (fun n => (if n ∈ p then f n else 0) +
      (if n ∈ p then 0 else f n)) = f := by
    funext n
    split_ifs <;> simp
  constructor
  · simpa only [he] using hw.add ht
  · have hh := hw.tsum_add ht
    rw [he] at hh
    rw [hh, tsum_eq_sum (s := p) (by intro n hn; simp [hn])]
    simp

/-- Nonzero residual indices in the symmetric finite window. -/
def residualWindow (N : ℕ) : Finset ℤ :=
  (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase 0

@[simp] theorem mem_residualWindow (N : ℕ) (n : ℤ) :
    n ∈ residualWindow N ↔ n ≠ 0 ∧ |n| ≤ (N : ℤ) := by
  simp [residualWindow, abs_le]

/-- The fixed inner convolution truncation supports any residual window up to 16385. -/
theorem residualWindow_cut {N : ℕ} (hN : N ≤ 16385) (n : ℤ)
    (hn : n ∈ residualWindow N) : 4*(n:ℝ)^2 < 32771^2 := by
  have ha : |(n : ℝ)| ≤ (16385 : ℝ) := by
    have h := (mem_residualWindow N n).mp hn |>.2
    have hb : |n| ≤ (16385 : ℤ) := h.trans (by exact_mod_cast hN)
    exact_mod_cast hb
  have hs := sq_le_sq₀ (abs_nonneg (n : ℝ)) (by norm_num : (0:ℝ) ≤ 16385) |>.mpr ha
  rw [sq_abs] at hs
  nlinarith

/-- The zero head contributes nothing when the window and the strict tail are combined. -/
theorem residual_window_tail_sum (s : ℝ) (N : ℕ)
    (ht : Summable (fun n : ℤ => if (N : ℤ) < |n| then
      headRealResidual s n ^ 2 / residualWeight n else 0)) :
    Summable (fun n : ℤ => headRealResidual s n ^ 2 / residualWeight n) ∧
      (∑' n : ℤ, headRealResidual s n ^ 2 / residualWeight n) =
        (∑ n ∈ residualWindow N, realResidual s n ^ 2 / residualWeight n) +
        ∑' n : ℤ, (if (N : ℤ) < |n| then
          headRealResidual s n ^ 2 / residualWeight n else 0) := by
  classical
  have he : (fun n : ℤ => if n ∈ residualWindow N then 0 else
      headRealResidual s n ^ 2 / residualWeight n) =
      (fun n : ℤ => if (N : ℤ) < |n| then
        headRealResidual s n ^ 2 / residualWeight n else 0) := by
    funext n
    by_cases h0 : n = 0
    · subst n; simp [headRealResidual]
    · by_cases hn : |n| ≤ (N : ℤ)
      · simp [h0, hn, not_lt.mpr hn]
      · simp [h0, hn, lt_of_not_ge hn]
  have h := finite_complement_sum
    (fun n => headRealResidual s n ^ 2 / residualWeight n) (residualWindow N)
    (by rwa [he])
  refine ⟨h.1, ?_⟩
  rw [h.2, he]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  simp only [headRealResidual, ite_eq_right ((mem_residualWindow N n).mp hn).1]

/-- A finite-window certificate and a tail budget imply the target lower bound.
The numerical energy certificate remains an explicit input. -/
theorem alphaStar_lower_of_window_tail (N : ℕ) (a e : ℤ → ℝ) (W B : ℝ)
    (hcut : ∀ n ∈ residualWindow N, 4*(n:ℝ)^2 < 32771^2)
    (happrox : ∀ n ∈ residualWindow N, |windowApproximation n - a n| ≤ e n)
    (hwindow : (∑ n ∈ residualWindow N,
      (|a n|+e n+windowApproximationError n)^2 / residualWeight n) ≤ W)
    (ht : Summable (fun n : ℤ => if (N : ℤ) < |n| then
      headRealResidual AlphaRemark.spectralUpper n ^ 2 / residualWeight n else 0))
    (htail : (∑' n : ℤ, if (N : ℤ) < |n| then
      headRealResidual AlphaRemark.spectralUpper n ^ 2 / residualWeight n else 0) ≤ B)
    (hbudget : W + B < (1628/1000000000 : ℝ))
    (henergy : (1628/1000000000 : ℝ) ≤ Qform AlphaRemark.spectralUpper trial) :
    (4323617/10000000 : ℝ) < Staircase.alphaStar := by
  have hsplit := residual_window_tail_sum AlphaRemark.spectralUpper N ht
  apply alphaStar_lower_of_residual_budget hsplit.1 _ henergy
  rw [hsplit.2]
  exact (add_le_add ((finite_residual_window_bound _ a e hcut happrox).trans hwindow)
    htail).trans_lt hbudget

end KsIndex.AlphaRemarkTrial
