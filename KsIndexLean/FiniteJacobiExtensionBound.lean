module

public import KsIndexLean.FiniteJacobiExtension
public import KsIndexLean.JacobiModeH1Bound

@[expose] public section


noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.DtNCircle

/-- Signed-mode orthogonality gives an exact Pythagorean identity for partial sums. -/
lemma finiteJacobiExtension_norm_sq {k : ℕ} (hk : 2 ≤ k) (s : Finset NZ) (a : NZ → ℂ) :
    ‖finiteJacobiExtension hk s a‖ ^ 2 =
      ∑ n ∈ s, ‖a n‖ ^ 2 * ‖normalizedJacobiMode hk n‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [finiteJacobiExtension]
  | @insert n s hn ih =>
    have ho : inner ℂ (a n • normalizedJacobiMode hk n)
        (finiteJacobiExtension hk s a) = 0 := by
      simp only [finiteJacobiExtension, inner_sum, inner_smul_left, inner_smul_right]
      apply Finset.sum_eq_zero
      intro m hm
      have hnm : n ≠ m := by intro he; exact hn (he ▸ hm)
      rw [normalizedJacobiMode_inner_eq_zero hk n m hnm, mul_zero, mul_zero]
    rw [show finiteJacobiExtension hk (insert n s) a =
      a n • normalizedJacobiMode hk n + finiteJacobiExtension hk s a by
        simp only [finiteJacobiExtension, Finset.sum_insert hn]]
    have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ ho
    simp only [← pow_two] at hp
    rw [hp, norm_smul, mul_pow, ih, Finset.sum_insert hn]

/-- The uniform bound needed to complete the Jacobi extension on H^(1/2). -/
lemma finiteJacobiExtension_norm_sq_le {k : ℕ} (hk : 2 ≤ k) (s : Finset NZ) (a : NZ → ℂ) :
    ‖finiteJacobiExtension hk s a‖ ^ 2 ≤
      jacobiModeH1Constant k * ∑ n ∈ s, (1 + |(n.val : ℝ)|) * ‖a n‖ ^ 2 := by
  rw [finiteJacobiExtension_norm_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have h := mul_le_mul_of_nonneg_left (normalizedJacobiMode_norm_sq_le hk n) (sq_nonneg ‖a n‖)
  nlinarith

end KsIndex.Trace
