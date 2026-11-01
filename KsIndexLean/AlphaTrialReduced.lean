module

public import KsIndexLean.AlphaTrialGroupReduction

@[expose] public section


/-! # Reduction of the trial Stieltjes sum

The 25-term Stieltjes combination is partitioned into four groups and reduced
to base transforms at orders 14 and 15. Each group has an explicit multiplier
and a prefix-plus-forcing remainder, with its normalization `1 / g β 0`
factored outside. The reduction assumes a positive transform parameter and
nonzero recurrence denominators; it does not identify the compensated residual. -/

noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ PowerArc KsIndex.AlphaRemarkTrial

/-- Multiplier obtained by summing the trial coefficients and recurrence factors over a group. -/
def trialGroupMult (s : Finset (Fin 25)) (β r_g z : ℝ) : ℝ :=
  ∑ i ∈ s, (coefficient i).re * (-1 : ℝ) ^ chainLen i *
    zChainCoeff β r_g z (chainLen i)

/-- Concrete group rest: the trial's prefix-plus-forcing at a group. -/
def trialGroupRest (s : Finset (Fin 25)) (β r_g z : ℝ) : ℝ :=
  ∑ i ∈ s, (coefficient i).re *
    ((∑ u ∈ Finset.range (chainLen i),
        (-1 : ℝ) ^ u * g β ((9 - (shift i : ℝ)) + 2 * u) / (z + u))
      + (-1 : ℝ) ^ chainLen i * zChainForce β r_g z (chainLen i))

/-- Membership facts for the four groups. -/
lemma grpAe_facts {i : Fin 25} (h : i ∈ grpAe) :
    exponent i = 4323618/10000000 ∧ baseR i = 15 := by
  rw [grpAe, Finset.mem_filter] at h
  exact ⟨h.2.1, baseR_even h.2.2⟩

lemma grpAo_facts {i : Fin 25} (h : i ∈ grpAo) :
    exponent i = 4323618/10000000 ∧ baseR i = 14 := by
  rw [grpAo, Finset.mem_filter] at h
  exact ⟨h.2.1, baseR_odd h.2.2⟩

lemma grpBe_facts {i : Fin 25} (h : i ∈ grpBe) :
    exponent i = 5676382/10000000 ∧ baseR i = 15 := by
  rw [grpBe, Finset.mem_filter] at h
  exact ⟨h.2.1, baseR_even h.2.2⟩

lemma grpBo_facts {i : Fin 25} (h : i ∈ grpBo) :
    exponent i = 5676382/10000000 ∧ baseR i = 14 := by
  rw [grpBo, Finset.mem_filter] at h
  exact ⟨h.2.1, baseR_odd h.2.2⟩

/-- One group's slice of the 25-term symbolic combination, reduced. -/
lemma group_slice_reduced (s : Finset (Fin 25)) (β r_g z : ℝ)
    (hβ : 0 < β) (hz : 0 < z)
    (hfacts : ∀ i ∈ s, exponent i = β ∧ baseR i = r_g)
    (hd : ∀ i ∈ s, ∀ u : ℕ, u < chainLen i →
      z + u + 1 - (baseR i - exponent i) / 2 ≠ 0) :
    (∑ i ∈ s, ((coefficient i).re / g (exponent i) 0) *
        powerArcStieltjes (exponent i) (9 - shift i) z) =
      (1 / g β 0) * (trialGroupMult s β r_g z * powerArcStieltjes β r_g z
        + trialGroupRest s β r_g z) := by
  have hstep : (∑ i ∈ s, ((coefficient i).re / g (exponent i) 0) *
      powerArcStieltjes (exponent i) (9 - shift i) z) =
      (1 / g β 0) * ∑ i ∈ s, (coefficient i).re *
        powerArcStieltjes β (9 - shift i) z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(hfacts i hi).1]
    ring
  rw [hstep, trial_group_reduction s β r_g z hβ hz
    (fun i hi => (hfacts i hi).1) (fun i hi => (hfacts i hi).2)
    (fun i hi u hu => by
      have := hd i hi u hu
      rwa [(hfacts i hi).1, (hfacts i hi).2] at this),
    trialGroupMult, trialGroupRest]

/-- The full 25-term Stieltjes combination reduces to four base transforms,
with each normalization `1 / g β 0` outside its group. Positivity of `z` and
nonvanishing of every recurrence denominator are explicit hypotheses. -/
theorem stieltjes_side_reduced (z : ℝ) (hz : 0 < z)
    (hd : ∀ i : Fin 25, ∀ u : ℕ, u < chainLen i →
      z + u + 1 - (baseR i - exponent i) / 2 ≠ 0) :
    (∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
        powerArcStieltjes (exponent i) (9 - shift i) z) =
      (1 / g (4323618/10000000) 0) *
        (trialGroupMult grpAe (4323618/10000000) 15 z *
            powerArcStieltjes (4323618/10000000) 15 z
          + trialGroupRest grpAe (4323618/10000000) 15 z
          + (trialGroupMult grpAo (4323618/10000000) 14 z *
              powerArcStieltjes (4323618/10000000) 14 z
            + trialGroupRest grpAo (4323618/10000000) 14 z))
      + (1 / g (5676382/10000000) 0) *
        (trialGroupMult grpBe (5676382/10000000) 15 z *
            powerArcStieltjes (5676382/10000000) 15 z
          + trialGroupRest grpBe (5676382/10000000) 15 z
          + (trialGroupMult grpBo (5676382/10000000) 14 z *
              powerArcStieltjes (5676382/10000000) 14 z
            + trialGroupRest grpBo (5676382/10000000) 14 z)) := by
  rw [sum_four_groups (fun i => ((coefficient i).re / g (exponent i) 0) *
    powerArcStieltjes (exponent i) (9 - shift i) z)]
  rw [group_slice_reduced grpAe _ 15 z (by norm_num) hz
      (fun i hi => grpAe_facts hi) (fun i hi => hd i),
    group_slice_reduced grpAo _ 14 z (by norm_num) hz
      (fun i hi => grpAo_facts hi) (fun i hi => hd i),
    group_slice_reduced grpBe _ 15 z (by norm_num) hz
      (fun i hi => grpBe_facts hi) (fun i hi => hd i),
    group_slice_reduced grpBo _ 14 z (by norm_num) hz
      (fun i hi => grpBo_facts hi) (fun i hi => hd i)]
  ring

end KsIndex.OppositeHalf
