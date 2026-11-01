module

public import KsIndexLean.NodeCTailArithmetic
public import KsIndexLean.NodeCCoeff
public import KsIndexLean.NodeCSigmaInf

@[expose] public section


/-! The trial-field Fourier coefficients satisfy the hypotheses of the
Aristotle-produced arithmetic tail estimate. Instantiating that estimate gives
summability and the rational upper bound for the weighted coefficient tail,
for `k ≥ 1` and `0 < a < 1`.
-/
noncomputable section
namespace KsIndex.NodeC
open KsIndex.Trace

lemma trialPsi_coeffData : AristotleTail.CoeffData
    (fun n : ℤ => ‖circleFourierCoeff trialPsi n‖ ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [trialPsi_coeff_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
  · simp only [trialPsi_coeff_neg_one, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
  · intro t ht
    exact trialPsi_normSq_even ht
  · intro t ht
    exact trialPsi_normSq_odd ht

lemma trialPsi_tail_summable {k : ℕ} (hk : 1 ≤ k) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    Summable (fun n : ℤ => ‖circleFourierCoeff trialPsi n‖ ^ 2 / sigma k a n) := by
  exact AristotleTail.tail_summable _ trialPsi_coeffData hk ha0 ha1

lemma trialPsi_tail_bound {k : ℕ} (hk : 1 ≤ k) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    (∑' n : ℤ, ‖circleFourierCoeff trialPsi n‖ ^ 2 / sigma k a n) ≤
      4 * Hs (a * (1 - a)) / 25 + 32 / 75 := by
  exact AristotleTail.tail_bound _ trialPsi_coeffData hk ha0 ha1

end KsIndex.NodeC
