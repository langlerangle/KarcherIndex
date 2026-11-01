module

public import KsIndexLean.AlphaFamilyTailEndpoints
public import KsIndexLean.AlphaTrialLeadingTail

@[expose] public section


/-! Fully finite endpoint bounds for the actual trial's inner truncation error. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open PowerArc AlphaResidual

def trialInnerUA (T : ℕ) : ℝ :=
  ∑ i : Fin 12, |(coefficient (familyIndexA i)).re / g (4323618/10000000) 0| *
    ((1+9/(2*(T:ℝ)+1))*|g (4323618/10000000) (2*(T:ℝ)+shift (familyIndexA i)+1)| /
      (2*((4323618/10000000)+1)))

def trialInnerUB (T : ℕ) : ℝ :=
  ∑ i : Fin 13, |(coefficient (familyIndexB i)).re / g (5676382/10000000) 0| *
    ((1+11/(2*(T:ℝ)+1))^2*|g (5676382/10000000) (2*(T:ℝ)+shift (familyIndexB i)+1)| /
      (2*((5676382/10000000)+2)*(2*(T:ℝ)+shift (familyIndexB i)+1+(5676382/10000000)+2)))

lemma trialInnerUA_bound (n : ℤ) (T : ℕ) (hT : 4 ≤ T) :
    (∑' k : ℕ, |signedFamilyTail convolutionA n T k|/(2*(T:ℝ)+1+2*k)) ≤ trialInnerUA T := by
  simp only [signedFamilyTail, abs_mul, abs_neg_one_zpow, one_mul]
  have ht : (4:ℝ) ≤ T := by exact_mod_cast hT
  have hx : (0:ℝ) < 2*(T:ℝ)+1 := by positivity
  apply family_linear_tail_endpoints (4323618/10000000) _ _ T (1+9/(2*(T:ℝ)+1))
    (by norm_num)
  · intro i
    fin_cases i <;> norm_num [familyIndexA, shift] <;> linarith
  · have h : (0:ℝ) ≤ 9/(2*(T:ℝ)+1) := by positivity
    linarith
  · intro i
    have he : (1+9/(2*(T:ℝ)+1))*(2*(T:ℝ)+1) = 2*(T:ℝ)+1+9 := by
      field_simp
    rw [he]
    fin_cases i <;> norm_num [familyIndexA, shift] <;> linarith

lemma trialInnerUB_bound (n : ℤ) (T : ℕ) (hT : 4 ≤ T) :
    (∑' k : ℕ, |signedFamilyTail convolutionB n T k|/(2*(T:ℝ)+1+2*k)^2) ≤ trialInnerUB T := by
  simp only [signedFamilyTail, abs_mul, abs_neg_one_zpow, one_mul]
  have ht : (4:ℝ) ≤ T := by exact_mod_cast hT
  have hx : (0:ℝ) < 2*(T:ℝ)+1 := by positivity
  apply family_square_tail_endpoints (5676382/10000000) _ _ T (1+11/(2*(T:ℝ)+1))
    (by norm_num)
  · intro i
    fin_cases i <;> norm_num [familyIndexB, shift] <;> linarith
  · have h : (0:ℝ) ≤ 11/(2*(T:ℝ)+1) := by positivity
    linarith
  · intro i
    have he : (1+11/(2*(T:ℝ)+1))*(2*(T:ℝ)+1) = 2*(T:ℝ)+1+11 := by
      field_simp
    rw [he]
    fin_cases i <;> norm_num [familyIndexB, shift] <;> linarith

/-- No infinite-sum estimates remain as hypotheses in this truncation bound. -/
theorem realResidual_finite_endpoint_error (s : ℝ) (n : ℤ) (T : ℕ)
    (hT : 4 ≤ T) (hcut : 4*(n:ℝ)^2 < (2*(T:ℝ)+1)^2) :
    |realResidual s n - correctedResidualCenter s n T| ≤
      s^2*(2/Real.pi)*(innerPairAMajorant n (2*(T:ℝ)+1)*trialInnerUA T +
        innerPairBMajorant n (2*(T:ℝ)+1)*trialInnerUB T) :=
  realResidual_correctedCenter_bound s n T _ _ hT hcut
    (trialInnerUA_bound n T hT) (trialInnerUB_bound n T hT)

end KsIndex.AlphaRemarkTrial
