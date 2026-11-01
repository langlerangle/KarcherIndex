module

public import KsIndexLean.AlphaTrialGroupReductionReflected
public import KsIndexLean.AlphaTrialReduced

@[expose] public section


/-! Reduction of the reflected Stieltjes sum to four base transforms. -/

noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ PowerArc KsIndex.AlphaRemarkTrial

/-- Multiplier obtained by summing the trial coefficients and recurrence factors over a group. -/
def trialGroupMultR (s : Finset (Fin 25)) (β r_g z : ℝ) : ℝ :=
  ∑ i ∈ s, (coefficient i).re * (-1 : ℝ) ^ chainLenR i *
    zChainCoeff β r_g z (chainLenR i)

/-- Concrete group rest: the trial's prefix-plus-forcing at a group. -/
def trialGroupRestR (s : Finset (Fin 25)) (β r_g z : ℝ) : ℝ :=
  ∑ i ∈ s, (coefficient i).re *
    ((∑ u ∈ Finset.range (chainLenR i),
        (-1 : ℝ) ^ u * g β ((9 + (shift i : ℝ)) + 2 * u) / (z + u))
      + (-1 : ℝ) ^ chainLenR i * zChainForce β r_g z (chainLenR i))

/-- One group's slice of the 25-term symbolic combination, reduced. -/
lemma group_slice_reduced_refl (s : Finset (Fin 25)) (β r_g z : ℝ)
    (hβ : 0 < β) (hz : 0 < z)
    (hfacts : ∀ i ∈ s, exponent i = β ∧ baseR i = r_g)
    (hd : ∀ i ∈ s, ∀ u : ℕ, u < chainLenR i →
      z + u + 1 - (baseR i - exponent i) / 2 ≠ 0) :
    (∑ i ∈ s, ((coefficient i).re / g (exponent i) 0) *
        powerArcStieltjes (exponent i) (9 + shift i) z) =
      (1 / g β 0) * (trialGroupMultR s β r_g z * powerArcStieltjes β r_g z
        + trialGroupRestR s β r_g z) := by
  have hstep : (∑ i ∈ s, ((coefficient i).re / g (exponent i) 0) *
      powerArcStieltjes (exponent i) (9 + shift i) z) =
      (1 / g β 0) * ∑ i ∈ s, (coefficient i).re *
        powerArcStieltjes β (9 + shift i) z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(hfacts i hi).1]
    ring
  rw [hstep, trial_group_reduction_refl s β r_g z hβ hz
    (fun i hi => (hfacts i hi).1) (fun i hi => (hfacts i hi).2)
    (fun i hi u hu => by
      have := hd i hi u hu
      rwa [(hfacts i hi).1, (hfacts i hi).2] at this),
    trialGroupMultR, trialGroupRestR]

/-- The full 25-term Stieltjes combination reduces to four base transforms,
with each normalization `1 / g β 0` outside its group. Positivity of `z` and
nonvanishing of every recurrence denominator are explicit hypotheses. -/
theorem stieltjes_side_reduced_refl (z : ℝ) (hz : 0 < z)
    (hd : ∀ i : Fin 25, ∀ u : ℕ, u < chainLenR i →
      z + u + 1 - (baseR i - exponent i) / 2 ≠ 0) :
    (∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
        powerArcStieltjes (exponent i) (9 + shift i) z) =
      (1 / g (4323618/10000000) 0) *
        (trialGroupMultR grpAe (4323618/10000000) 15 z *
            powerArcStieltjes (4323618/10000000) 15 z
          + trialGroupRestR grpAe (4323618/10000000) 15 z
          + (trialGroupMultR grpAo (4323618/10000000) 14 z *
              powerArcStieltjes (4323618/10000000) 14 z
            + trialGroupRestR grpAo (4323618/10000000) 14 z))
      + (1 / g (5676382/10000000) 0) *
        (trialGroupMultR grpBe (5676382/10000000) 15 z *
            powerArcStieltjes (5676382/10000000) 15 z
          + trialGroupRestR grpBe (5676382/10000000) 15 z
          + (trialGroupMultR grpBo (5676382/10000000) 14 z *
              powerArcStieltjes (5676382/10000000) 14 z
            + trialGroupRestR grpBo (5676382/10000000) 14 z)) := by
  rw [sum_four_groups (fun i => ((coefficient i).re / g (exponent i) 0) *
    powerArcStieltjes (exponent i) (9 + shift i) z)]
  rw [group_slice_reduced_refl grpAe _ 15 z (by norm_num) hz
      (fun i hi => grpAe_facts hi) (fun i hi => hd i),
    group_slice_reduced_refl grpAo _ 14 z (by norm_num) hz
      (fun i hi => grpAo_facts hi) (fun i hi => hd i),
    group_slice_reduced_refl grpBe _ 15 z (by norm_num) hz
      (fun i hi => grpBe_facts hi) (fun i hi => hd i),
    group_slice_reduced_refl grpBo _ 14 z (by norm_num) hz
      (fun i hi => grpBo_facts hi) (fun i hi => hd i)]
  ring

end KsIndex.OppositeHalf
