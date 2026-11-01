module

public import KsIndexLean.AlphaGroupMultiplierBridgeReflected
public import KsIndexLean.AlphaTrialCompensatedNegative

@[expose] public section


/-! Reflection signs of the trial's four finite multiplier groups. -/
noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ PowerArc KsIndex.AlphaRemarkTrial

lemma grpAe_chain_reflection (F : ℕ → ℝ) :
    (∑ i ∈ grpAe, (coefficient i).re * F (chainLenR i)) =
      -(∑ i ∈ grpAe, (coefficient i).re * F (chainLen i)) := by
  simp [grpAe, Finset.sum_filter, Fin.sum_univ_succ, coefficient, exponent, shift,
    chainLenR, chainLen, baseShift]
  ring

lemma grpAe_mult_reflection (β r z : ℝ) :
    trialGroupMultR grpAe β r z = -(trialGroupMult grpAe β r z) := by
  rw [trialGroupMultR_eq_normalized, trialGroupMult_eq_normalized]
  exact grpAe_chain_reflection _

lemma grpAo_chain_reflection (F : ℕ → ℝ) :
    (∑ i ∈ grpAo, (coefficient i).re * F (chainLenR i)) =
      -(∑ i ∈ grpAo, (coefficient i).re * F (chainLen i)) := by
  simp [grpAo, Finset.sum_filter, Fin.sum_univ_succ, coefficient, exponent, shift,
    chainLenR, chainLen, baseShift]
  ring

lemma grpAo_mult_reflection (β r z : ℝ) :
    trialGroupMultR grpAo β r z = -(trialGroupMult grpAo β r z) := by
  rw [trialGroupMultR_eq_normalized, trialGroupMult_eq_normalized]
  exact grpAo_chain_reflection _

lemma grpBe_chain_reflection (F : ℕ → ℝ) :
    (∑ i ∈ grpBe, (coefficient i).re * F (chainLenR i)) =
      (∑ i ∈ grpBe, (coefficient i).re * F (chainLen i)) := by
  simp [grpBe, Finset.sum_filter, Fin.sum_univ_succ, coefficient, exponent, shift,
    chainLenR, chainLen, baseShift]
  ring

lemma grpBe_mult_reflection (β r z : ℝ) :
    trialGroupMultR grpBe β r z = (trialGroupMult grpBe β r z) := by
  rw [trialGroupMultR_eq_normalized, trialGroupMult_eq_normalized]
  exact grpBe_chain_reflection _

lemma grpBo_chain_reflection (F : ℕ → ℝ) :
    (∑ i ∈ grpBo, (coefficient i).re * F (chainLenR i)) =
      (∑ i ∈ grpBo, (coefficient i).re * F (chainLen i)) := by
  simp [grpBo, Finset.sum_filter, Fin.sum_univ_succ, coefficient, exponent, shift,
    chainLenR, chainLen, baseShift]
  ring

lemma grpBo_mult_reflection (β r z : ℝ) :
    trialGroupMultR grpBo β r z = (trialGroupMult grpBo β r z) := by
  rw [trialGroupMultR_eq_normalized, trialGroupMult_eq_normalized]
  exact grpBo_chain_reflection _

end KsIndex.OppositeHalf
