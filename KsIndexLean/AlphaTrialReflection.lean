module

public import KsIndexLean.AlphaRemarkTrial

@[expose] public section


/-! Exact reflection identities for the two exponent families in the trial.

Reflection is about the half-integer lattice center. The identities retain
signed coefficients and do not require assumptions about their signs.
-/

noncomputable section
namespace KsIndex.AlphaRemarkTrial
open PowerArc

def familyIndexA (i : Fin 12) : Fin 25 := ⟨i.val, by omega⟩
def familyIndexB (i : Fin 13) : Fin 25 := ⟨12 + i.val, by omega⟩

def familyConvolution {ι : Type*} [Fintype ι]
    (β : ℝ) (d : ι → ℤ) (a : ι → ℝ) (m : ℤ) : ℝ :=
  ∑ i, a i * (g β (2 * (m : ℝ) + d i + 1) / g β 0)

theorem familyConvolution_reflect {ι : Type*} [Fintype ι]
    (β ε : ℝ) (d : ι → ℤ) (a : ι → ℝ) (e : Equiv.Perm ι)
    (hd : ∀ i, d (e i) = -d i) (ha : ∀ i, a (e i) = ε * a i) (m : ℤ) :
    familyConvolution β d a (-m-1) = ε * familyConvolution β d a m := by
  unfold familyConvolution
  rw [← Equiv.sum_comp e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hd, ha]
  push_cast
  rw [show 2 * (-(m : ℝ) - 1) + -(d i : ℝ) + 1 =
      -(2 * (m : ℝ) + d i + 1) by ring, g_neg]
  ring

lemma familyA_shift_reflect (i : Fin 12) :
    shift (familyIndexA i.rev) = -shift (familyIndexA i) := by
  fin_cases i <;> norm_num [familyIndexA, shift, Fin.rev]

lemma familyB_shift_reflect (i : Fin 13) :
    shift (familyIndexB i.rev) = -shift (familyIndexB i) := by
  fin_cases i <;> norm_num [familyIndexB, shift, Fin.rev]

lemma familyA_coefficient_reflect (i : Fin 12) :
    (coefficient (familyIndexA i.rev)).re = -(coefficient (familyIndexA i)).re := by
  fin_cases i <;> norm_num [familyIndexA, coefficient, Fin.rev]

lemma familyB_coefficient_reflect (i : Fin 13) :
    (coefficient (familyIndexB i.rev)).re = (coefficient (familyIndexB i)).re := by
  fin_cases i <;> norm_num [familyIndexB, coefficient, Fin.rev]

def convolutionA : ℤ → ℝ := familyConvolution (4323618/10000000)
  (fun i : Fin 12 => shift (familyIndexA i))
  (fun i : Fin 12 => (coefficient (familyIndexA i)).re)

def convolutionB : ℤ → ℝ := familyConvolution (5676382/10000000)
  (fun i : Fin 13 => shift (familyIndexB i))
  (fun i : Fin 13 => (coefficient (familyIndexB i)).re)

theorem convolutionA_reflect (m : ℤ) : convolutionA (-m-1) = -convolutionA m := by
  have hh := familyConvolution_reflect (4323618/10000000) (-1)
    (fun i : Fin 12 => shift (familyIndexA i))
    (fun i : Fin 12 => (coefficient (familyIndexA i)).re) Fin.revPerm
    familyA_shift_reflect (fun i => by simpa using familyA_coefficient_reflect i) m
  simpa [convolutionA] using hh

theorem convolutionB_reflect (m : ℤ) : convolutionB (-m-1) = convolutionB m := by
  have hh := familyConvolution_reflect (5676382/10000000) 1
    (fun i : Fin 13 => shift (familyIndexB i))
    (fun i : Fin 13 => (coefficient (familyIndexB i)).re) Fin.revPerm
    familyB_shift_reflect (fun i => by simpa using familyB_coefficient_reflect i) m
  simpa [convolutionB] using hh

lemma familyA_exponent (i : Fin 12) :
    exponent (familyIndexA i) = (4323618/10000000 : ℝ) := by
  fin_cases i <;> norm_num [familyIndexA, exponent]

lemma familyB_exponent (i : Fin 13) :
    exponent (familyIndexB i) = (5676382/10000000 : ℝ) := by
  fin_cases i <;> norm_num [familyIndexB, exponent]

/-- The two reflected families are the real components of the actual trial
convolution, not independent auxiliary sequences. -/
theorem convS_trial_re_eq_families (m : ℤ) :
    (CircleQ.convS trial m).re = convolutionA m + convolutionB m := by
  rw [convS_trial]
  change Complex.reAddGroupHom (∑ i : Fin 25, coefficient i *
    (g (exponent i) (2 * (m : ℝ) + (shift i + 1)) / g (exponent i) 0 : ℝ)) = _
  rw [map_sum, Fin.sum_univ_add (a := 12) (b := 13)]
  unfold convolutionA convolutionB familyConvolution
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    change (coefficient (familyIndexA i) *
      (g (exponent (familyIndexA i)) (2 * (m : ℝ) + (shift (familyIndexA i) + 1)) /
        g (exponent (familyIndexA i)) 0 : ℝ)).re = _
    rw [familyA_exponent]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, add_assoc]
  · apply Finset.sum_congr rfl
    intro i _
    change (coefficient (familyIndexB i) *
      (g (exponent (familyIndexB i)) (2 * (m : ℝ) + (shift (familyIndexB i) + 1)) /
        g (exponent (familyIndexB i)) 0 : ℝ)).re = _
    rw [familyB_exponent]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, add_assoc]

end KsIndex.AlphaRemarkTrial
