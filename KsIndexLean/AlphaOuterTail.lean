module

public import KsIndexLean.AlphaTrialResidualCertificate

@[expose] public section


/-! # Weighted residual tails from pointwise majorants

A nonnegative bound `b` for `|realResidual s n|` on `|n| > T`, with a
summable weighted square, bounds the corresponding tail of
`headRealResidual s n ^ 2 / residualWeight n`. The tail excludes zero, where
the head-adjusted residual differs. `AlphaOuterTailAssembly` constructs the
majorant from compensated groups and side-specific remainder bounds.
-/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual

/-- Generic weighted tail bound from a pointwise residual majorant on `|n| > T`. -/
theorem weighted_tail_le (s : ℝ) (T : ℕ) (b : ℤ → ℝ) (hbnn : ∀ n, 0 ≤ b n)
    (hb : ∀ n : ℤ, (T : ℤ) < |n| → |realResidual s n| ≤ b n)
    (hsum : Summable (fun n : ℤ => if (T : ℤ) < |n| then b n ^ 2 / residualWeight n else 0)) :
    Summable (fun n : ℤ => if (T : ℤ) < |n| then headRealResidual s n ^ 2 / residualWeight n else 0) ∧
      (∑' n : ℤ, (if (T : ℤ) < |n| then headRealResidual s n ^ 2 / residualWeight n else 0))
        ≤ ∑' n : ℤ, (if (T : ℤ) < |n| then b n ^ 2 / residualWeight n else 0) := by
  have hle : ∀ n : ℤ,
      (if (T : ℤ) < |n| then headRealResidual s n ^ 2 / residualWeight n else 0)
        ≤ (if (T : ℤ) < |n| then b n ^ 2 / residualWeight n else 0) := by
    intro n
    split_ifs with hn
    · have hn0 : n ≠ 0 := by rintro rfl; rw [abs_zero] at hn; omega
      have hw := residualWeight_pos n
      have hsq : realResidual s n ^ 2 ≤ b n ^ 2 := by
        have h := abs_le.mp (hb n hn); nlinarith [h.1, h.2, hbnn n]
      simp only [headRealResidual, if_neg hn0, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr hw.le)
    · exact le_refl 0
  have hnn : ∀ n : ℤ,
      0 ≤ (if (T : ℤ) < |n| then headRealResidual s n ^ 2 / residualWeight n else 0) := by
    intro n
    split_ifs with hn
    · exact div_nonneg (sq_nonneg _) (residualWeight_pos n).le
    · exact le_refl 0
  have hLsum : Summable
      (fun n : ℤ => if (T : ℤ) < |n| then headRealResidual s n ^ 2 / residualWeight n else 0) :=
    Summable.of_nonneg_of_le hnn hle hsum
  exact ⟨hLsum, hLsum.tsum_le_tsum hle hsum⟩

end KsIndex.AlphaRemarkTrial

#print axioms KsIndex.AlphaRemarkTrial.weighted_tail_le
