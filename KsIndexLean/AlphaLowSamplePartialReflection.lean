module

public import KsIndexLean.AlphaTrialTableData

@[expose] public section


/-! Exact odd/even decomposition and reflection of the trial sample numerator. -/
namespace KsIndex.AlphaRemarkTrial

/-- The odd block: the first 12 coefficient terms of the sample numerator. -/
def partialSumA (t : CoefficientTable) (k : ℤ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin 25 => i.val < 12),
    coefficientNumerator i * tableCellA t i (k + shift i) * cellZ i (k + shift i)

/-- The even block: the last 13 coefficient terms of the sample numerator. -/
def partialSumB (t : CoefficientTable) (k : ℤ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin 25 => ¬ i.val < 12),
    coefficientNumerator i * tableCellA t i (k + shift i) * cellZ i (k + shift i)

/-- The split is exact: A + B is the existing sample numerator. -/
theorem partialSum_add (t : CoefficientTable) (k : ℤ) :
    partialSumA t k + partialSumB t k = tableSampleNumerator t k := by
  unfold partialSumA partialSumB tableSampleNumerator
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- Cell evenness: the coefficient cell depends on k only through |k|. -/
theorem tableCellA_neg (t : CoefficientTable) (i : Fin 25) (m : ℤ) :
    tableCellA t i (-m) = tableCellA t i m := by
  simp [tableCellA, Int.natAbs_neg]

/-- Seed-factor evenness. -/
theorem cellZ_neg (i : Fin 25) (m : ℤ) : cellZ i (-m) = cellZ i m := by
  simp [cellZ, Int.natAbs_neg]

/-- Total odd-block reflection: pairs i ↦ 11 − i inside `i.val < 12`, identity outside. -/
def reflectA (i : Fin 25) : Fin 25 :=
  if h : i.val < 12 then ⟨11 - i.val, by omega⟩ else i

/-- Total even-block reflection: identity inside `i.val < 12`, pairs i ↦ 36 − i outside
(there 12 ≤ i.val ≤ 24, so 12 ≤ 36 − i.val ≤ 24 < 25). -/
def reflectB (i : Fin 25) : Fin 25 :=
  if h : i.val < 12 then i else ⟨36 - i.val, by omega⟩

/-- Pairing data facts for the odd block (stated on the total reflection). -/
theorem pairA_facts : ∀ i : Fin 25, i.val < 12 →
    coefficientNumerator (reflectA i) = -coefficientNumerator i ∧
    shift (reflectA i) = -shift i ∧
    numerator (reflectA i) = numerator i ∧
    seedNumerator (reflectA i) = seedNumerator i := by
  decide

/-- Pairing data facts for the even block (stated on the total reflection). -/
theorem pairB_facts : ∀ i : Fin 25, ¬ i.val < 12 →
    coefficientNumerator (reflectB i) = coefficientNumerator i ∧
    shift (reflectB i) = -shift i ∧
    numerator (reflectB i) = numerator i ∧
    seedNumerator (reflectB i) = seedNumerator i := by
  decide

theorem reflectA_mem {i : Fin 25} (h : i.val < 12) : (reflectA i).val < 12 := by
  simp only [reflectA, dif_pos h]
  omega

theorem reflectB_mem {i : Fin 25} (h : ¬ i.val < 12) : ¬ (reflectB i).val < 12 := by
  simp only [reflectB, dif_neg h]
  omega

theorem reflectA_invol {i : Fin 25} (h : i.val < 12) : reflectA (reflectA i) = i := by
  have h' := reflectA_mem h
  apply Fin.ext
  simp only [reflectA, dif_pos h] at h' ⊢
  simp only [dif_pos h']
  omega

theorem reflectB_invol {i : Fin 25} (h : ¬ i.val < 12) : reflectB (reflectB i) = i := by
  have h' := reflectB_mem h
  apply Fin.ext
  simp only [reflectB, dif_neg h] at h' ⊢
  simp only [dif_neg h']
  omega

/-- Cell factors are block-constant: `tableCellA` sees `i` only through `numerator i`,
`cellZ` only through `seedNumerator i`. -/
theorem tableCellA_congr (t : CoefficientTable) {i j : Fin 25}
    (h : numerator i = numerator j) (m : ℤ) : tableCellA t i m = tableCellA t j m := by
  simp [tableCellA, h]

theorem cellZ_congr {i j : Fin 25}
    (h : seedNumerator i = seedNumerator j) (m : ℤ) : cellZ i m = cellZ j m := by
  simp [cellZ, h]

/-- Pointwise: the odd-block term at −k equals the negative of the reflected term at k. -/
theorem termA_reflect (t : CoefficientTable) (k : ℤ) {i : Fin 25} (h : i.val < 12) :
    coefficientNumerator i * tableCellA t i (-k + shift i) * cellZ i (-k + shift i) =
      -(coefficientNumerator (reflectA i) *
        tableCellA t (reflectA i) (k + shift (reflectA i)) *
        cellZ (reflectA i) (k + shift (reflectA i))) := by
  obtain ⟨hc, hs, hn, hz⟩ := pairA_facts i h
  have harg : k + shift (reflectA i) = -(-k + shift i) := by
    rw [hs]; ring
  rw [harg, tableCellA_neg, cellZ_neg,
    tableCellA_congr t hn, cellZ_congr hz, hc]
  ring

/-- Pointwise: the even-block term at −k equals the reflected term at k. -/
theorem termB_reflect (t : CoefficientTable) (k : ℤ) {i : Fin 25} (h : ¬ i.val < 12) :
    coefficientNumerator i * tableCellA t i (-k + shift i) * cellZ i (-k + shift i) =
      coefficientNumerator (reflectB i) *
        tableCellA t (reflectB i) (k + shift (reflectB i)) *
        cellZ (reflectB i) (k + shift (reflectB i)) := by
  obtain ⟨hc, hs, hn, hz⟩ := pairB_facts i h
  have harg : k + shift (reflectB i) = -(-k + shift i) := by
    rw [hs]; ring
  rw [harg, tableCellA_neg, cellZ_neg,
    tableCellA_congr t hn, cellZ_congr hz, hc]

/-- The partial sum A is odd in k. -/
theorem partialSumA_neg (t : CoefficientTable) (k : ℤ) :
    partialSumA t (-k) = -partialSumA t k := by
  unfold partialSumA
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_nbij' reflectA reflectA ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact reflectA_mem hi
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact reflectA_mem hi
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact reflectA_invol hi
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact reflectA_invol hi
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact termA_reflect t k hi

/-- The partial sum B is even in k. -/
theorem partialSumB_neg (t : CoefficientTable) (k : ℤ) :
    partialSumB t (-k) = partialSumB t k := by
  unfold partialSumB
  refine Finset.sum_nbij' reflectB reflectB ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact reflectB_mem hi
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact reflectB_mem hi
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact reflectB_invol hi
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact reflectB_invol hi
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact termB_reflect t k hi

/-- The sample numerators at k and −k are respectively A+B and −A+B. -/
theorem tableSampleNumerator_eq_partialSums (t : CoefficientTable) (k : ℤ) :
    tableSampleNumerator t k = partialSumA t k + partialSumB t k :=
  (partialSum_add t k).symm

theorem tableSampleNumerator_neg_eq (t : CoefficientTable) (k : ℤ) :
    tableSampleNumerator t (-k) = -partialSumA t k + partialSumB t k := by
  rw [← partialSum_add, partialSumA_neg, partialSumB_neg]

end KsIndex.AlphaRemarkTrial
