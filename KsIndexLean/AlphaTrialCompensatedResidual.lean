module

public import KsIndexLean.AlphaTrialOppositeReduced
public import KsIndexLean.AlphaTrialHomogeneousReduced

@[expose] public section


/-! Exact compensated-group decomposition of the positive-index trial residual. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ PowerArc OppositeHalf

def groupCorrection (p : Finset (Fin 25)) (β r z : ℝ) : ℝ :=
  trialGroupRest p β r z / g β 0 + trialGroupMult p β r z *
    (stieltjesCorrectionC β r 1 / z + stieltjesCorrectionD β r 1 / z^2)

def groupCompensated (p : Finset (Fin 25)) (β r κ w : ℝ) (n : ℕ) : ℝ :=
  trialGroupMult p β r ((n : ℝ)+9/2) * compensatedPowerArcGroup β r κ w n

def allGroupCorrections (z : ℝ) : ℝ :=
  groupCorrection grpAe (4323618/10000000) 15 z + groupCorrection grpAo (4323618/10000000) 14 z + (groupCorrection grpBe (5676382/10000000) 15 z + groupCorrection grpBo (5676382/10000000) 14 z)

def allCompensatedGroups (κ w : ℝ) (n : ℕ) : ℝ :=
  groupCompensated grpAe (4323618/10000000) 15 κ w n + groupCompensated grpAo (4323618/10000000) 14 κ w n + (groupCompensated grpBe (5676382/10000000) 15 κ w n + groupCompensated grpBo (5676382/10000000) 14 κ w n)

lemma group_compensation_identity (p : Finset (Fin 25)) (β r κ w : ℝ) (n : ℕ) :
    (-1 : ℝ)^n * w * (g β (2*(n : ℝ)+9-r)/g β 0) *
        trialGroupMult p β r ((n : ℝ)+9/2) -
      κ * ((trialGroupMult p β r ((n : ℝ)+9/2) *
        powerArcStieltjes β r ((n : ℝ)+9/2) + trialGroupRest p β r ((n : ℝ)+9/2)) / g β 0) =
      groupCompensated p β r κ w n - κ * groupCorrection p β r ((n : ℝ)+9/2) := by
  unfold groupCompensated groupCorrection compensatedPowerArcGroup compensatedStieltjes
    stieltjesCorrectionD stieltjesCorrectionC
  rw [show 2*((n : ℝ)+9/2)-r = 2*(n : ℝ)+9-r by ring]
  ring

lemma all_group_compensation_identity (κ w : ℝ) (n : ℕ) :
    (-1 : ℝ)^n * w * reducedTrial n - κ * reducedMomentLower ((n : ℝ)+9/2) =
      allCompensatedGroups κ w n - κ * allGroupCorrections ((n : ℝ)+9/2) := by
  have h0 := group_compensation_identity grpAe (4323618/10000000) 15 κ w n
  have h1 := group_compensation_identity grpAo (4323618/10000000) 14 κ w n
  have h2 := group_compensation_identity grpBe (5676382/10000000) 15 κ w n
  have h3 := group_compensation_identity grpBo (5676382/10000000) 14 κ w n
  simp only [show (2*(n : ℝ)+9-15) = 2*(n : ℝ)-6 by ring,
    show (2*(n : ℝ)+9-14) = 2*(n : ℝ)-5 by ring] at h0 h1 h2 h3
  unfold reducedTrial reducedMomentLower allCompensatedGroups allGroupCorrections
  linear_combination h0 + h1 + h2 + h3

/-- Finite remainder after subtracting the compensated base-transform groups. -/
def rawRemainder (n : ℝ) : ℝ :=
  6*reflectedMass - (6*n+1-4/(6*n+1))*reflectedMomentPrefix (n+1/2)
    - 4/(6*n+1)*(reflectedMomentPrefix (1/3)+reducedMomentLower (13/3))
    + 12/(6*n+1)*(trialMomentPrefix +
        (reducedMomentUpper (14/3)+reducedMomentLower (13/3))/6)
    - (6*n+1-4/(6*n+1))*allGroupCorrections (n+9/2)

def scaledRemainder (s n : ℝ) : ℝ := (2*s^2/Real.pi)*rawRemainder n

/-- Actual positive-index residual, with every compensated term and remainder identified. -/
theorem realResidual_eq_compensated (s : ℝ) (n : ℕ) (hn : 3 ≤ n) :
    realResidual s (n : ℤ) = (-1 : ℝ)^n *
      (sigP (n : ℤ) * allCompensatedGroups (2*s^2/Real.pi) (1+s^2) n +
        scaledRemainder s n) := by
  have hnZ : (3 : ℤ) ≤ n := by exact_mod_cast hn
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [realResidual_eq_reduced s n (by omega), trial_re_eq_reduced n hnZ]
  have hc := all_group_compensation_identity (2*s^2/Real.pi) (1+s^2) n
  have hs : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by rw [← mul_pow]; norm_num
  simp only [Int.cast_natCast, zpow_natCast] at *
  unfold reducedOpposite scaledRemainder rawRemainder
  rw [abs_of_pos (show (0 : ℝ)<6*n+1 by positivity)]
  have hsig : sigP (n : ℤ) = 6*(n : ℝ)+1-4/(6*(n : ℝ)+1) := by
    unfold sigP
    simp only [Int.cast_natCast]
    rw [abs_of_pos (by positivity)]
    field_simp
  rw [hsig]
  simp only [Int.cast_natCast, zpow_natCast, div_mul_eq_div_div]
  linear_combination (-1 : ℝ)^n * (6*(n : ℝ)+1-4/(6*(n : ℝ)+1)) * hc -
    (1+s^2)*(6*(n : ℝ)+1-4/(6*(n : ℝ)+1))*reducedTrial n * hs

end KsIndex.AlphaRemarkTrial
