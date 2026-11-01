module

public import KsIndexLean.AlphaTrialGroups

@[expose] public section


/-! # Group reduction for the trial

The trial's 25 terms are partitioned by exponent and shift parity into four
groups. Within each group, the Stieltjes recurrence gives an explicit multiplier
and remainder at a common base index. Group membership supplies the exponent and
base-index facts; the reduction retains its denominator nonvanishing hypotheses.
-/

noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ PowerArc KsIndex.AlphaRemarkTrial

/-- Reduce a term set with constant exponent and base index to one base
transform plus an explicit remainder. The sums here are unnormalized;
normalization by `1 / g β 0` is applied by consumers. -/
theorem trial_group_reduction (s : Finset (Fin 25)) (β r_g z : ℝ)
    (hβ : 0 < β) (hz : 0 < z)
    (hexp : ∀ i ∈ s, exponent i = β) (hbase : ∀ i ∈ s, baseR i = r_g)
    (hd : ∀ i ∈ s, ∀ u : ℕ, u < chainLen i → z + u + 1 - (r_g - β) / 2 ≠ 0) :
    (∑ i ∈ s, (coefficient i).re * powerArcStieltjes β (9 - shift i) z) =
      (∑ i ∈ s, (coefficient i).re * (-1 : ℝ) ^ chainLen i *
          zChainCoeff β r_g z (chainLen i)) * powerArcStieltjes β r_g z
      + ∑ i ∈ s, (coefficient i).re *
          ((∑ u ∈ Finset.range (chainLen i),
              (-1 : ℝ) ^ u * g β ((9 - (shift i : ℝ)) + 2 * u) / (z + u))
            + (-1 : ℝ) ^ chainLen i * zChainForce β r_g z (chainLen i)) := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hri : β ≤ 9 - (shift i : ℝ) := by
    rw [← hexp i hi]
    exact exponent_le_baseterm i
  have hterm := paS_iter hβ hri hz (chainLen i)
  have hrel : (9 - (shift i : ℝ)) + 2 * (chainLen i : ℝ) = r_g := by
    rw [← hbase i hi]
    exact chainLen_rel i
  rw [hrel] at hterm
  have hrg : β ≤ r_g := by
    rw [← hrel]
    have := Nat.cast_nonneg (α := ℝ) (chainLen i)
    linarith
  have hchain := paS_z_chain hβ hrg hz (chainLen i) (hd i hi)
  rw [hterm, hchain]
  ring

/-- The four parity groups, defined by their predicates. -/
def grpAe : Finset (Fin 25) :=
  Finset.univ.filter fun i => exponent i = 4323618/10000000 ∧ shift i % 2 = 0
def grpAo : Finset (Fin 25) :=
  Finset.univ.filter fun i => exponent i = 4323618/10000000 ∧ shift i % 2 ≠ 0
def grpBe : Finset (Fin 25) :=
  Finset.univ.filter fun i => exponent i = 5676382/10000000 ∧ shift i % 2 = 0
def grpBo : Finset (Fin 25) :=
  Finset.univ.filter fun i => exponent i = 5676382/10000000 ∧ shift i % 2 ≠ 0

lemma exponent_dichotomy (i : Fin 25) :
    exponent i = 4323618/10000000 ∨ exponent i = 5676382/10000000 := by
  fin_cases i <;> norm_num [exponent]

/-- Every term lies in exactly one group: the four-way partition of any
25-indexed sum. -/
lemma sum_four_groups (F : Fin 25 → ℝ) :
    (∑ i : Fin 25, F i) =
      (∑ i ∈ grpAe, F i) + (∑ i ∈ grpAo, F i)
      + ((∑ i ∈ grpBe, F i) + (∑ i ∈ grpBo, F i)) := by
  classical
  have hA : (∑ i ∈ Finset.univ.filter
      (fun i : Fin 25 => exponent i = 4323618/10000000), F i) =
      (∑ i ∈ grpAe, F i) + (∑ i ∈ grpAo, F i) := by
    rw [grpAe, grpAo, ← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter fun i : Fin 25 => exponent i = 4323618/10000000)
      (fun i => shift i % 2 = 0) F, Finset.filter_filter, Finset.filter_filter]
  have hB : (∑ i ∈ Finset.univ.filter
      (fun i : Fin 25 => ¬ exponent i = 4323618/10000000), F i) =
      (∑ i ∈ grpBe, F i) + (∑ i ∈ grpBo, F i) := by
    have hBeq : Finset.univ.filter
        (fun i : Fin 25 => ¬ exponent i = 4323618/10000000) =
        Finset.univ.filter (fun i : Fin 25 => exponent i = 5676382/10000000) := by
      apply Finset.filter_congr
      intro i _
      rcases exponent_dichotomy i with h | h <;> simp [h] <;> norm_num
    rw [hBeq, grpBe, grpBo, ← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter fun i : Fin 25 => exponent i = 5676382/10000000)
      (fun i => shift i % 2 = 0) F, Finset.filter_filter, Finset.filter_filter]
  rw [← hA, ← hB, Finset.sum_filter_add_sum_filter_not]

/-- Base indices per group: even-shift groups sit at `r_g = 15`, odd at `14`. -/
lemma baseR_even {i : Fin 25} (h : shift i % 2 = 0) : baseR i = 15 := by
  rw [baseR, baseShift, if_pos h]
  norm_num

lemma baseR_odd {i : Fin 25} (h : shift i % 2 ≠ 0) : baseR i = 14 := by
  rw [baseR, baseShift, if_neg h]
  norm_num

end KsIndex.OppositeHalf
