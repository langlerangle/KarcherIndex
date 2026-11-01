module

public import KsIndexLean.AlphaTrialNegativeReduced
public import KsIndexLean.AlphaTrialHomogeneousNegative

@[expose] public section


/-! Exact compensated-group decomposition of the negative-index trial residual. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ PowerArc OppositeHalf

def groupCorrectionR (p : Finset (Fin 25)) (β r z : ℝ) : ℝ :=
  trialGroupRestR p β r z / g β 0 + trialGroupMultR p β r z *
    (stieltjesCorrectionC β r 1 / z + stieltjesCorrectionD β r 1 / z^2)

def groupCompensatedR (p : Finset (Fin 25)) (β r κ w : ℝ) (n : ℕ) : ℝ :=
  trialGroupMultR p β r ((n : ℝ)+9/2) * compensatedPowerArcGroup β r κ w n

def allGroupCorrectionsR (z : ℝ) : ℝ :=
  groupCorrectionR grpAe (4323618/10000000) 15 z + groupCorrectionR grpAo (4323618/10000000) 14 z + (groupCorrectionR grpBe (5676382/10000000) 15 z + groupCorrectionR grpBo (5676382/10000000) 14 z)

def allCompensatedGroupsR (κ w : ℝ) (n : ℕ) : ℝ :=
  groupCompensatedR grpAe (4323618/10000000) 15 κ w n + groupCompensatedR grpAo (4323618/10000000) 14 κ w n + (groupCompensatedR grpBe (5676382/10000000) 15 κ w n + groupCompensatedR grpBo (5676382/10000000) 14 κ w n)

lemma group_compensation_identity_refl (p : Finset (Fin 25)) (β r κ w : ℝ) (n : ℕ) :
    (-1 : ℝ)^n * w * (g β (2*(n : ℝ)+9-r)/g β 0) *
        trialGroupMultR p β r ((n : ℝ)+9/2) -
      κ * ((trialGroupMultR p β r ((n : ℝ)+9/2) *
        powerArcStieltjes β r ((n : ℝ)+9/2) + trialGroupRestR p β r ((n : ℝ)+9/2)) / g β 0) =
      groupCompensatedR p β r κ w n - κ * groupCorrectionR p β r ((n : ℝ)+9/2) := by
  unfold groupCompensatedR groupCorrectionR compensatedPowerArcGroup compensatedStieltjes
    stieltjesCorrectionD stieltjesCorrectionC
  rw [show 2*((n : ℝ)+9/2)-r = 2*(n : ℝ)+9-r by ring]
  ring

lemma all_group_compensation_identity_refl (κ w : ℝ) (n : ℕ) :
    (-1 : ℝ)^n * w * reducedTrialNegative n - κ * reducedMomentUpper ((n : ℝ)+9/2) =
      allCompensatedGroupsR κ w n - κ * allGroupCorrectionsR ((n : ℝ)+9/2) := by
  have h0 := group_compensation_identity_refl grpAe (4323618/10000000) 15 κ w n
  have h1 := group_compensation_identity_refl grpAo (4323618/10000000) 14 κ w n
  have h2 := group_compensation_identity_refl grpBe (5676382/10000000) 15 κ w n
  have h3 := group_compensation_identity_refl grpBo (5676382/10000000) 14 κ w n
  simp only [show (2*(n : ℝ)+9-15) = 2*(n : ℝ)-6 by ring,
    show (2*(n : ℝ)+9-14) = 2*(n : ℝ)-5 by ring] at h0 h1 h2 h3
  unfold reducedTrialNegative reducedMomentUpper allCompensatedGroupsR allGroupCorrectionsR
  linear_combination h0 + h1 + h2 + h3

/-- Finite remainder after subtracting the compensated base-transform groups. -/
def rawRemainderNegative (n : ℝ) : ℝ :=
  6*positiveMass - (6*n-1-4/(6*n-1))*positiveMomentPrefix (n+1/2)
    - 4/(6*n-1)*(positiveMomentPrefix (2/3)+reducedMomentUpper (14/3))
    + 12/(6*n-1)*(trialMomentPrefix +
        (reducedMomentUpper (14/3)+reducedMomentLower (13/3))/6)
    - (6*n-1-4/(6*n-1))*allGroupCorrectionsR (n+9/2)

def scaledRemainderNegative (s n : ℝ) : ℝ := (2*s^2/Real.pi)*rawRemainderNegative n

/-- Actual negative-index residual, with every compensated term and remainder identified. -/
theorem realResidual_neg_eq_compensated (s : ℝ) (n : ℕ) (hn : 3 ≤ n) :
    realResidual s (-(n : ℤ)) = (-1 : ℝ)^n *
      (sigP (-(n : ℤ)) * allCompensatedGroupsR (2*s^2/Real.pi) (1+s^2) n +
        scaledRemainderNegative s n) := by
  have hnZ : (3 : ℤ) ≤ n := by exact_mod_cast hn
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [realResidual_neg_eq_reduced s n (by omega), trial_neg_re_eq_reduced n hnZ]
  have hc := all_group_compensation_identity_refl (2*s^2/Real.pi) (1+s^2) n
  have hs : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by rw [← mul_pow]; norm_num
  simp only [Int.cast_natCast, zpow_natCast] at *
  unfold reducedNegativeOpposite scaledRemainderNegative rawRemainderNegative
  rw [abs_of_neg (show 6*(-(n : ℝ))+1 < 0 by linarith),
    show -(6*(-(n : ℝ))+1) = 6*(n : ℝ)-1 by ring]
  have hsig : sigP (-(n : ℤ)) = 6*(n : ℝ)-1-4/(6*(n : ℝ)-1) := by
    unfold sigP
    simp only [Int.cast_natCast, Int.cast_neg]
    rw [abs_of_neg (show 6*(-(n : ℝ))+1 < 0 by linarith),
      show -(6*(-(n : ℝ))+1) = 6*(n : ℝ)-1 by ring]
    have hL : 6*(n : ℝ)-1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hsig]
  simp only [Int.cast_natCast, zpow_natCast, div_mul_eq_div_div]
  linear_combination (-1 : ℝ)^n * (6*(n : ℝ)-1-4/(6*(n : ℝ)-1)) * hc -
    (1+s^2)*(6*(n : ℝ)-1-4/(6*(n : ℝ)-1))*reducedTrialNegative n * hs

end KsIndex.AlphaRemarkTrial
