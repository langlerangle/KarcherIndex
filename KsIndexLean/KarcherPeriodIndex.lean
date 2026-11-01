module

public import KsIndexLean.KarcherLoopFormula

@[expose] public section


/-! Actual real periods and their integer index; no period hypotheses are assumed. -/
open scoped BigOperators
noncomputable section
namespace KsIndex.KarcherData
open Piecewise

def periodVector (k : ℕ) (C : Chain) : ℝ × ℝ × ℝ :=
  ((C.contour (coeff1 k)).re, (C.contour (coeff2 k)).re, (C.contour (coeff3 k)).re)

def periodSet (k : ℕ) : Set (ℝ × ℝ × ℝ) :=
  {p | ∃ C : Chain, C.IsClosed ∧ (∀ z ∈ Surface.punctures k, C.Avoids z) ∧
    p = periodVector k C}

def endSign (k : ℕ) (z : ℂ) : ℤ := if z ^ k = Complex.I then 1 else -1

lemma residue3_real_endSign {k : ℕ} {z : ℂ} (hz : z ∈ Surface.punctures k) :
    ((2 * Real.pi * Complex.I) * (1 / z ^ k)).re =
      (2 * Real.pi) * (endSign k z : ℝ) := by
  rcases puncture_power_sign hz with h | h
  · simp [endSign, h, Complex.mul_re, Complex.mul_im]
  · have hn : z ^ k ≠ Complex.I := by
      rw [h]
      intro he
      have := congrArg Complex.im he
      norm_num at this
    simp only [endSign, ite_eq_right hn]
    simp [h, Complex.mul_re, Complex.mul_im]

def periodIndex {k : ℕ} (hk : 2 ≤ k) (C : Chain) (hc : C.IsClosed)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) : ℤ :=
  ∑ z : punctureFinset k,
    C.winding hc z.val (hA z.val ((mem_punctureFinset hk).mp z.property)) * endSign k z.val

lemma integer_residue_real (n : ℤ) (R : ℂ) :
    ((2 * Real.pi * Complex.I) * ((n : ℂ) * R)).re =
      (n : ℝ) * ((2 * Real.pi * Complex.I) * R).re := by
  rw [show (2 * Real.pi * Complex.I) * ((n : ℂ) * R) =
    (n : ℂ) * ((2 * Real.pi * Complex.I) * R) by ring]
  simp [Complex.mul_re]

lemma windingSum_real {k : ℕ} (hk : 2 ≤ k) (C : Chain) (hc : C.IsClosed)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) (R : ℂ → ℂ) :
    ((2 * Real.pi * Complex.I) * karcherWindingSum hk C hc hA R).re =
    ∑ z : punctureFinset k,
      (C.winding hc z.val (hA z.val ((mem_punctureFinset hk).mp z.property)) : ℝ) *
        ((2 * Real.pi * Complex.I) * R z.val).re := by
  simp only [karcherWindingSum, Chain.residueWindingSum, Finset.mul_sum,
    Complex.re_sum, integer_residue_real]

theorem periodVector_eq_index {k : ℕ} (hk : 2 ≤ k) (C : Chain) (hc : C.IsClosed)
    (hA : ∀ z ∈ Surface.punctures k, C.Avoids z) :
    periodVector k C = (0, 0, (2 * Real.pi) * (periodIndex hk C hc hA : ℝ)) := by
  unfold periodVector
  rw [coeff1_loop_formula hk C hc hA, coeff2_loop_formula hk C hc hA,
    coeff3_loop_formula hk C hc hA]
  simp only [windingSum_real, residue1_real_factor, residue2_real_factor, mul_zero,
    Finset.sum_const_zero]
  congr 2
  simp only [periodIndex, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [residue3_real_endSign ((mem_punctureFinset hk).mp z.property)]
  ring

theorem periodSet_subset {k : ℕ} (hk : 2 ≤ k) :
    periodSet k ⊆ {p | ∃ n : ℤ, p = (0, 0, (2 * Real.pi) * (n : ℝ))} := by
  rintro p ⟨C, hc, hA, rfl⟩
  exact ⟨periodIndex hk C hc hA, periodVector_eq_index hk C hc hA⟩

end KsIndex.KarcherData
