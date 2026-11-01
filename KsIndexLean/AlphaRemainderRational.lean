module

public import KsIndexLean.AlphaRemainderPrefix
public import KsIndexLean.AlphaGroupSeedRest

@[expose] public section


/-! # Finite-remainder identities in rational and shared-seed form

Expresses `rawRemainder` and `rawRemainderNegative` using mass, a weighted
finite prefix, signed and reduced moments, and four group corrections.
Both forward and reflected group corrections are written with explicit
rational factors and normalized endpoint values of `g`.

The shared-seed identities express the integer endpoint values using
`g β 1 / g β 0`, for `β > 0`. They provide the symbolic input to numerical
seed-error estimates. These are identities for the finite remainder;
outer-tail estimates are supplied separately.
-/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ PowerArc OppositeHalf

/-! ### Rational form of the four group corrections (normalized endpoints) -/

/-- One forward group's correction in explicit rational form (normalized endpoints). -/
def groupCorrectionRat (p : Finset (Fin 25)) (β r z : ℝ) : ℝ :=
  rationalGroupRest p β r z (fun i => (coefficient i).re) (fun i => 9 - shift i) chainLen
      (fun t => g β t / g β 0)
    + trialGroupMult p β r z * (g β r / g β 0) * rationalCorrectionUnit β r z

/-- One reflected group's correction in explicit rational form. -/
def groupCorrectionRatR (p : Finset (Fin 25)) (β r z : ℝ) : ℝ :=
  rationalGroupRest p β r z (fun i => (coefficient i).re) (fun i => 9 + shift i) chainLenR
      (fun t => g β t / g β 0)
    + trialGroupMultR p β r z * (g β r / g β 0) * rationalCorrectionUnit β r z

theorem groupCorrection_eq_groupCorrectionRat (p : Finset (Fin 25)) (β r z : ℝ) :
    groupCorrection p β r z = groupCorrectionRat p β r z := by
  unfold groupCorrectionRat
  exact groupCorrection_eq_rational p β r z

/-- Reflected analogue of `groupCorrection_eq_rational`. -/
theorem groupCorrectionR_eq_groupCorrectionRatR (p : Finset (Fin 25)) (β r z : ℝ) :
    groupCorrectionR p β r z = groupCorrectionRatR p β r z := by
  unfold groupCorrectionR groupCorrectionRatR
  rw [trialGroupRestR_normalized]
  unfold rationalCorrectionUnit stieltjesCorrectionD stieltjesCorrectionC
  ring

/-! ### Rational form of the whole group-correction sums -/

def allGroupCorrectionsRat (z : ℝ) : ℝ :=
  groupCorrectionRat grpAe (4323618/10000000) 15 z +
    groupCorrectionRat grpAo (4323618/10000000) 14 z +
    (groupCorrectionRat grpBe (5676382/10000000) 15 z +
      groupCorrectionRat grpBo (5676382/10000000) 14 z)

def allGroupCorrectionsRatR (z : ℝ) : ℝ :=
  groupCorrectionRatR grpAe (4323618/10000000) 15 z +
    groupCorrectionRatR grpAo (4323618/10000000) 14 z +
    (groupCorrectionRatR grpBe (5676382/10000000) 15 z +
      groupCorrectionRatR grpBo (5676382/10000000) 14 z)

theorem allGroupCorrections_eq_rational (z : ℝ) :
    allGroupCorrections z = allGroupCorrectionsRat z := by
  unfold allGroupCorrections allGroupCorrectionsRat
  rw [groupCorrection_eq_groupCorrectionRat, groupCorrection_eq_groupCorrectionRat,
    groupCorrection_eq_groupCorrectionRat, groupCorrection_eq_groupCorrectionRat]

theorem allGroupCorrectionsR_eq_rational (z : ℝ) :
    allGroupCorrectionsR z = allGroupCorrectionsRatR z := by
  unfold allGroupCorrectionsR allGroupCorrectionsRatR
  rw [groupCorrectionR_eq_groupCorrectionRatR, groupCorrectionR_eq_groupCorrectionRatR,
    groupCorrectionR_eq_groupCorrectionRatR, groupCorrectionR_eq_groupCorrectionRatR]

/-! ### The complete remainder formula (rational level)

Every term explicit: mass, weighted finite prefix, actual moment constants, and the fully
rationalized group corrections (forward + reflected). -/

theorem rawRemainder_eq_rational (n : ℝ) (hn : 1 ≤ n) :
    rawRemainder n =
      6*(reflectedMass - ∑ t ∈ Finset.range 4, reflectedDemod t) +
      2*(∑ t ∈ Finset.range 4,
        reflectedDemod t*((6*(t : ℝ)+2)-4/(6*(t : ℝ)+2))/(2*(t : ℝ)+2*n+1)) +
      (12*signedTrialMoment - 4*reducedMomentLower (13/3))/(6*n+1) -
      (6*n+1-4/(6*n+1))*allGroupCorrectionsRat (n+9/2) := by
  rw [rawRemainder_eq_weighted_prefix n hn, allGroupCorrections_eq_rational]

theorem rawRemainderNegative_eq_rational (n : ℝ) (hn : 1 ≤ n) :
    rawRemainderNegative n =
      6*(positiveMass - ∑ t ∈ Finset.range 4, positiveDemod t) +
      2*(∑ t ∈ Finset.range 4,
        positiveDemod t*((6*(t : ℝ)+4)-4/(6*(t : ℝ)+4))/(2*(t : ℝ)+2*n+1)) +
      (12*signedTrialMoment - 4*reducedMomentUpper (14/3))/(6*n-1) -
      (6*n-1-4/(6*n-1))*allGroupCorrectionsRatR (n+9/2) := by
  rw [rawRemainderNegative_eq_weighted_prefix n hn, allGroupCorrectionsR_eq_rational]

/-! ### Shared-seed form of the group corrections

The group rests use the single common odd seed `g β 1 / g β 0`; the reciprocal-correction base value
`g β r / g β 0` at integer `r` is the same seed's `integerSeedValue`. -/

def groupCorrectionSeed (p : Finset (Fin 25)) (β : ℝ) (r : ℤ) (z : ℝ) : ℝ :=
  seededGroupRest p β r z (g β 1 / g β 0) (fun i => (coefficient i).re)
      (fun i => 9 - shift i) chainLen
    + trialGroupMult p β (r : ℝ) z * integerSeedValue β (g β 1 / g β 0) r *
      rationalCorrectionUnit β (r : ℝ) z

def groupCorrectionSeedR (p : Finset (Fin 25)) (β : ℝ) (r : ℤ) (z : ℝ) : ℝ :=
  seededGroupRest p β r z (g β 1 / g β 0) (fun i => (coefficient i).re)
      (fun i => 9 + shift i) chainLenR
    + trialGroupMultR p β (r : ℝ) z * integerSeedValue β (g β 1 / g β 0) r *
      rationalCorrectionUnit β (r : ℝ) z

theorem groupCorrection_eq_seeded (p : Finset (Fin 25)) {β : ℝ} (hβ : 0 < β) (r : ℤ) (z : ℝ) :
    groupCorrection p β (r : ℝ) z = groupCorrectionSeed p β r z := by
  rw [groupCorrection_eq_groupCorrectionRat]
  unfold groupCorrectionRat groupCorrectionSeed
  rw [← trialGroupRest_normalized, trialGroupRest_eq_seeded p hβ r z,
    normalized_g_integer_seed hβ r]

theorem groupCorrectionR_eq_seeded (p : Finset (Fin 25)) {β : ℝ} (hβ : 0 < β) (r : ℤ) (z : ℝ) :
    groupCorrectionR p β (r : ℝ) z = groupCorrectionSeedR p β r z := by
  rw [groupCorrectionR_eq_groupCorrectionRatR]
  unfold groupCorrectionRatR groupCorrectionSeedR
  rw [← trialGroupRestR_normalized, trialGroupRestR_eq_seeded p hβ r z,
    normalized_g_integer_seed hβ r]

end KsIndex.AlphaRemarkTrial

#print axioms KsIndex.AlphaRemarkTrial.groupCorrectionR_eq_groupCorrectionRatR
#print axioms KsIndex.AlphaRemarkTrial.rawRemainder_eq_rational
#print axioms KsIndex.AlphaRemarkTrial.rawRemainderNegative_eq_rational
#print axioms KsIndex.AlphaRemarkTrial.groupCorrection_eq_seeded
#print axioms KsIndex.AlphaRemarkTrial.groupCorrectionR_eq_seeded
