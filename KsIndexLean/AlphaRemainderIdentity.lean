module

public import KsIndexLean.AlphaRemainderRational
public import KsIndexLean.AlphaRemainderSeedMass
public import KsIndexLean.AlphaRemainderGroupBounds

@[expose] public section


/-! # Algebraic decomposition of the raw remainder

For `n ≥ 1`, split `rawRemainder` and `rawRemainderNegative` into four parity-group
blocks and a moment term, with constants `Upos` and `Uneg`. Each group block
combines mass endpoints, a finite demodulated prefix, and a rational correction.
This module proves the regrouping identities; identifying these blocks with
`grpValue_*` and bounding the resulting remainder require separate results. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open OppositeHalf PowerArc CircleQ

/-- Positive-side moment constant (numerator of the `U`-term over `6n+1`). -/
def Upos : ℝ := 12*signedTrialMoment - 4*reducedMomentLower (13/3)

/-- Negative-side moment constant (numerator of the `U`-term over `6n-1`). -/
def Uneg : ℝ := 12*signedTrialMoment - 4*reducedMomentUpper (14/3)

/-- Per-index reflected-mass endpoint term. -/
def endpointMass (i : Fin 25) : ℝ :=
  ((coefficient i).re / g (exponent i) 0) *
    (((9-(shift i : ℝ))+exponent i) * g (exponent i) (9-(shift i : ℝ)) / (2*exponent i))

/-- The reflected mass minus its four-term demod prefix is the `Fin 25` endpoint sum
(definitional: `reflectedMass` is that prefix plus this sum). -/
lemma reflectedMass_sub_demod_eq_endpoint :
    reflectedMass - ∑ t ∈ Finset.range 4, reflectedDemod t = ∑ i : Fin 25, endpointMass i := by
  unfold reflectedMass endpointMass
  ring

/-- The mass block splits over the four parity groups. -/
lemma mass_split :
    reflectedMass - ∑ t ∈ Finset.range 4, reflectedDemod t =
      (∑ i ∈ grpAe, endpointMass i) + (∑ i ∈ grpAo, endpointMass i)
      + ((∑ i ∈ grpBe, endpointMass i) + (∑ i ∈ grpBo, endpointMass i)) := by
  rw [reflectedMass_sub_demod_eq_endpoint]
  exact sum_four_groups endpointMass

/-- The demod prefix block restricted to one parity group. -/
def demodGroup (p : Finset (Fin 25)) (n : ℝ) : ℝ :=
  ∑ t ∈ Finset.range 4,
    ((-1 : ℝ)^t * ∑ i ∈ p, (coefficient i).re *
      (g (exponent i) ((2*(t:ℝ)+1)-(shift i : ℝ)) / g (exponent i) 0))
    * ((6*(t:ℝ)+2)-4/(6*(t:ℝ)+2)) / (2*(t:ℝ)+2*n+1)

/-- The demod prefix block splits over the four parity groups. -/
lemma demod_block_split (n : ℝ) :
    (∑ t ∈ Finset.range 4, reflectedDemod t
        * ((6*(t:ℝ)+2)-4/(6*(t:ℝ)+2)) / (2*(t:ℝ)+2*n+1)) =
      demodGroup grpAe n + demodGroup grpAo n + (demodGroup grpBe n + demodGroup grpBo n) := by
  unfold demodGroup
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [reflectedDemod_eq_sum,
    sum_four_groups (fun i => (coefficient i).re *
      (g (exponent i) ((2*(t:ℝ)+1)-(shift i : ℝ)) / g (exponent i) 0))]
  ring

/-- The raw remainder is the sum of four group blocks (mass + demodulated
prefix − `sig`·correction) and the moment term. This identity only regroups the
rational expression; it does not identify polynomial coefficient arrays. -/
lemma rawRemainder_regrouped (n : ℝ) (hn : 1 ≤ n) :
    rawRemainder n =
      (6*(∑ i ∈ grpAe, endpointMass i) + 2*demodGroup grpAe n
          - (6*n+1-4/(6*n+1))*groupCorrectionRat grpAe (4323618/10000000) 15 (n+9/2))
      + (6*(∑ i ∈ grpAo, endpointMass i) + 2*demodGroup grpAo n
          - (6*n+1-4/(6*n+1))*groupCorrectionRat grpAo (4323618/10000000) 14 (n+9/2))
      + ((6*(∑ i ∈ grpBe, endpointMass i) + 2*demodGroup grpBe n
          - (6*n+1-4/(6*n+1))*groupCorrectionRat grpBe (5676382/10000000) 15 (n+9/2))
      + (6*(∑ i ∈ grpBo, endpointMass i) + 2*demodGroup grpBo n
          - (6*n+1-4/(6*n+1))*groupCorrectionRat grpBo (5676382/10000000) 14 (n+9/2)))
      + Upos/(6*n+1) := by
  rw [rawRemainder_eq_rational n hn, mass_split, demod_block_split]
  unfold allGroupCorrectionsRat Upos
  ring

/-! ### Negative residual side (mirror of the positive side) -/

/-- Per-index positive-mass endpoint term (negative residual side). -/
def endpointMassPos (i : Fin 25) : ℝ :=
  ((coefficient i).re / g (exponent i) 0) *
    (((9+(shift i : ℝ))+exponent i) * g (exponent i) (9+(shift i : ℝ)) / (2*exponent i))

/-- The positive mass minus its demod prefix is the `Fin 25` endpoint sum (definitional). -/
lemma positiveMass_sub_demod_eq_endpoint :
    positiveMass - ∑ t ∈ Finset.range 4, positiveDemod t = ∑ i : Fin 25, endpointMassPos i := by
  unfold positiveMass endpointMassPos
  ring

/-- The negative-side mass block splits over the four parity groups. -/
lemma massPos_split :
    positiveMass - ∑ t ∈ Finset.range 4, positiveDemod t =
      (∑ i ∈ grpAe, endpointMassPos i) + (∑ i ∈ grpAo, endpointMassPos i)
      + ((∑ i ∈ grpBe, endpointMassPos i) + (∑ i ∈ grpBo, endpointMassPos i)) := by
  rw [positiveMass_sub_demod_eq_endpoint]
  exact sum_four_groups endpointMassPos

/-- The negative-side demod prefix block restricted to one parity group. -/
def demodGroupPos (p : Finset (Fin 25)) (n : ℝ) : ℝ :=
  ∑ t ∈ Finset.range 4,
    ((-1 : ℝ)^t * ∑ i ∈ p, (coefficient i).re *
      (g (exponent i) ((2*(t:ℝ)+1)+(shift i : ℝ)) / g (exponent i) 0))
    * ((6*(t:ℝ)+4)-4/(6*(t:ℝ)+4)) / (2*(t:ℝ)+2*n+1)

/-- The negative-side demod prefix block splits over the four parity groups. -/
lemma demod_block_split_neg (n : ℝ) :
    (∑ t ∈ Finset.range 4, positiveDemod t
        * ((6*(t:ℝ)+4)-4/(6*(t:ℝ)+4)) / (2*(t:ℝ)+2*n+1)) =
      demodGroupPos grpAe n + demodGroupPos grpAo n
        + (demodGroupPos grpBe n + demodGroupPos grpBo n) := by
  unfold demodGroupPos
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [positiveDemod_eq_sum,
    sum_four_groups (fun i => (coefficient i).re *
      (g (exponent i) ((2*(t:ℝ)+1)+(shift i : ℝ)) / g (exponent i) 0))]
  ring

/-- Regrouping identity for the negative residual side. -/
lemma rawRemainderNegative_regrouped (n : ℝ) (hn : 1 ≤ n) :
    rawRemainderNegative n =
      (6*(∑ i ∈ grpAe, endpointMassPos i) + 2*demodGroupPos grpAe n
          - (6*n-1-4/(6*n-1))*groupCorrectionRatR grpAe (4323618/10000000) 15 (n+9/2))
      + (6*(∑ i ∈ grpAo, endpointMassPos i) + 2*demodGroupPos grpAo n
          - (6*n-1-4/(6*n-1))*groupCorrectionRatR grpAo (4323618/10000000) 14 (n+9/2))
      + ((6*(∑ i ∈ grpBe, endpointMassPos i) + 2*demodGroupPos grpBe n
          - (6*n-1-4/(6*n-1))*groupCorrectionRatR grpBe (5676382/10000000) 15 (n+9/2))
      + (6*(∑ i ∈ grpBo, endpointMassPos i) + 2*demodGroupPos grpBo n
          - (6*n-1-4/(6*n-1))*groupCorrectionRatR grpBo (5676382/10000000) 14 (n+9/2)))
      + Uneg/(6*n-1) := by
  rw [rawRemainderNegative_eq_rational n hn, massPos_split, demod_block_split_neg]
  unfold allGroupCorrectionsRatR Uneg
  ring

end KsIndex.AlphaRemarkTrial

#print axioms KsIndex.AlphaRemarkTrial.reflectedMass_sub_demod_eq_endpoint
#print axioms KsIndex.AlphaRemarkTrial.mass_split
#print axioms KsIndex.AlphaRemarkTrial.demod_block_split
#print axioms KsIndex.AlphaRemarkTrial.rawRemainder_regrouped
#print axioms KsIndex.AlphaRemarkTrial.positiveMass_sub_demod_eq_endpoint
#print axioms KsIndex.AlphaRemarkTrial.massPos_split
#print axioms KsIndex.AlphaRemarkTrial.demod_block_split_neg
#print axioms KsIndex.AlphaRemarkTrial.rawRemainderNegative_regrouped
