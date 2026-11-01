module

public import KsIndexLean.StaircaseIncrements
public import KsIndexLean.KarcherGeometricCapstone

@[expose] public section


/-! Successive indices of the six-ended EW quotients. -/
noncomputable section
namespace KsIndex.Staircase

lemma modelIndex_int_formula (m : ℕ) (hm : 1 ≤ m) :
    (modelIndex m : ℤ) = 6*(m : ℤ)-4*⌊(m : ℝ)*alphaStar⌋-3 := by
  have h := modelIndex_add m hm
  have hz : (modelIndex m : ℤ) + 4*(⌊(m : ℝ)*alphaStar⌋₊ : ℤ)+3 = 6*(m : ℤ) := by
    exact_mod_cast h
  rw [Int.natCast_floor_eq_floor (mul_nonneg (Nat.cast_nonneg _) alphaStar_pos.le)] at hz
  omega

lemma modelIndex_step (m : ℕ) (hm : 1 ≤ m) :
    modelIndex (m+1) = modelIndex m+2 ∨ modelIndex (m+1) = modelIndex m+6 := by
  have h := StaircaseIncrements.index_step alphaStar_pos.le
    (show alphaStar ≤ 1 by linarith [alphaStar_lt_half]) m
  have h0 := modelIndex_int_formula m hm
  have h1 := modelIndex_int_formula (m+1) (by omega)
  push_cast at h h0 h1
  omega

/-- An eventually periodic sequence of index increments forces a rational threshold. -/
theorem alphaStar_rational_of_periodic_modelIndex {N p : ℕ} (hp : 0 < p)
    (hperiod : ∀ n, N ≤ n →
      (modelIndex (n + p + 1) : ℤ) - (modelIndex (n + p) : ℤ) =
      (modelIndex (n + 1) : ℤ) - (modelIndex n : ℤ)) :
    ∃ q : ℚ, alphaStar = q :=
  StaircaseIncrements.rational_of_eventually_periodic_index
    (fun n => (modelIndex n : ℤ)) modelIndex_int_formula hp hperiod

end KsIndex.Staircase
namespace KsIndex.KarcherData.PaperHalfPeriodRealization

lemma geometricIndex_three_eq_staircase [Fact (2 ≤ 3)]
    (R : PaperHalfPeriodRealization 3) (m : ℕ) [NeZero m] :
    R.geometricIndex (m := m) = (Staircase.modelIndex m : ℕ∞) := by
  rw [R.geometricIndex_eq_model]
  exact Spectral.indSurface_three_eq_model m

/-- Increasing the period count by one increases the index by two or six.
The formula includes resonant threshold values. -/
theorem geometricIndex_three_step [Fact (2 ≤ 3)]
    (R : PaperHalfPeriodRealization 3) (m : ℕ) [NeZero m] :
    R.geometricIndex (m := m+1) = R.geometricIndex (m := m)+2 ∨
    R.geometricIndex (m := m+1) = R.geometricIndex (m := m)+6 := by
  rw [R.geometricIndex_three_eq_staircase, R.geometricIndex_three_eq_staircase]
  rcases Staircase.modelIndex_step m (Nat.pos_of_ne_zero (NeZero.ne m)) with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

/-- Natural-valued geometric indices, starting with the one-period quotient. -/
def geometricIndexSequence [Fact (2 ≤ 3)] (R : PaperHalfPeriodRealization 3) (n : ℕ) : ℕ :=
  (R.geometricIndex (m := n+1)).toNat

lemma geometricIndexSequence_eq [Fact (2 ≤ 3)] (R : PaperHalfPeriodRealization 3) (n : ℕ) :
    R.geometricIndexSequence n = Staircase.modelIndex (n+1) := by
  simp [geometricIndexSequence, R.geometricIndex_three_eq_staircase]

/-- Eventual periodicity of the actual geometric index increments implies
rationality of the critical phase. No irrationality assertion is made. -/
theorem alphaStar_rational_of_periodic_geometricIndex [Fact (2 ≤ 3)]
    (R : PaperHalfPeriodRealization 3) {N p : ℕ} (hp : 0 < p)
    (hperiod : ∀ n, N ≤ n →
      (R.geometricIndexSequence (n + p + 1) : ℤ) - (R.geometricIndexSequence (n + p) : ℤ) =
      (R.geometricIndexSequence (n + 1) : ℤ) - (R.geometricIndexSequence n : ℤ)) :
    ∃ q : ℚ, Staircase.alphaStar = q := by
  apply Staircase.alphaStar_rational_of_periodic_modelIndex (N := N+1) hp
  intro n hn
  have hh := hperiod (n-1) (by omega)
  simp only [R.geometricIndexSequence_eq] at hh
  have e1 : n-1+p+1+1 = n+p+1 := by omega
  have e2 : n-1+p+1 = n+p := by omega
  have e3 : n-1+1+1 = n+1 := by omega
  have e4 : n-1+1 = n := by omega
  rw [e1, e2, e3, e4] at hh
  exact hh

end KsIndex.KarcherData.PaperHalfPeriodRealization

#print axioms KsIndex.Staircase.alphaStar_rational_of_periodic_modelIndex
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.geometricIndex_three_step

open KsIndex.KarcherData.PaperHalfPeriodRealization in
#print axioms alphaStar_rational_of_periodic_geometricIndex
