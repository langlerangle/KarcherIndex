module

/-
# Translation witnesses resolved by character

For `k = 3`, the translation fields are resolved into eigenspaces of the
step-two shift and the rotation action. Every family constructed by
`symFam` is fixed by the step-two shift, since adding two preserves parity.
Thus `J3`, `Jplus = J1 + i·J2` and `Jminus = J1 - i·J2` lie in phase zero.

Their rotation eigenvalues are respectively `1`, `ζ₃` and `ζ₃²`.
The horizontal profiles are `2w²/D` and `2·conj(w²)/D`; the identity
`rotUnit 3 ^ 2 = ζ₃` fixes the orientation convention. The parity sign
in the vertical family is preserved by both actions.

The fields are elements of `BoundedJacobi 3 m` by construction. This file
proves their eigenspace memberships after uncurrying and proves each is
nonzero using the linear independence of the three translation fields.
-/
public import KsIndexLean.JacobiFamily
public import KsIndexLean.SurfaceSym
public import KsIndexLean.CharDecomp

@[expose] public section


noncomputable section
namespace KsIndex.JacobiFamily
open KsIndex.Surface KsIndex.SurfaceSym KsIndex.JacobiFields

variable {m : ℕ}

/-- The rotation-eigenvector combinations of the horizontal witnesses. -/
def Jplus (m : ℕ) : BoundedJacobi 3 m :=
  J1 3 m (by norm_num) + Complex.I • J2 3 m (by norm_num)

def Jminus (m : ℕ) : BoundedJacobi 3 m :=
  J1 3 m (by norm_num) - Complex.I • J2 3 m (by norm_num)

/-! ### The rotation unit: norm, punctures, and the ζ₃ identities -/

lemma rotUnit_norm_mul (w : ℂ) : ‖((rotUnit 3 : Circle) : ℂ) * w‖ = ‖w‖ := by
  rw [norm_mul]
  simp

lemma rotUnit_pow_six : ((rotUnit 3 : Circle) : ℂ) ^ 6 = 1 := by
  have h3 : ((rotUnit 3 : Circle) : ℂ) ^ 3 = 1 := rotUnit_pow (by norm_num)
  rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, h3, one_pow]

lemma rotUnit_mem_punctures_iff (w : ℂ) :
    ((rotUnit 3 : Circle) : ℂ) * w ∈ Surface.punctures 3
      ↔ w ∈ Surface.punctures 3 := by
  simp only [Surface.punctures, Set.mem_ofPred_eq, mul_pow]
  rw [show (2 * 3 : ℕ) = 6 by norm_num, rotUnit_pow_six, one_mul]

/-- `ζ₃ · rotUnit 3 = 1`: the rotation unit is the inverse third root. -/
lemma zeta_mul_rotUnit : FormIndex.zeta 3 * ((rotUnit 3 : Circle) : ℂ) = 1 := by
  unfold FormIndex.zeta rotUnit
  rw [Circle.coe_exp, ← Complex.exp_add, ← Complex.exp_zero]
  congr 1
  push_cast
  ring

/-- `rotUnit 3 ² = ζ₃`, fixing the rotation-character convention. -/
lemma rotUnit_sq : ((rotUnit 3 : Circle) : ℂ) ^ 2 = FormIndex.zeta 3 := by
  have h3 : ((rotUnit 3 : Circle) : ℂ) ^ 3 = 1 := rotUnit_pow (by norm_num)
  calc ((rotUnit 3 : Circle) : ℂ) ^ 2
      = ((rotUnit 3 : Circle) : ℂ) ^ 2
          * (FormIndex.zeta 3 * ((rotUnit 3 : Circle) : ℂ)) := by
        rw [zeta_mul_rotUnit, mul_one]
    _ = FormIndex.zeta 3 * ((rotUnit 3 : Circle) : ℂ) ^ 3 := by ring
    _ = FormIndex.zeta 3 := by rw [h3, mul_one]

/-- `conj ζ₃ = ζ₃²` (unimodular inverse). -/
lemma conj_zeta_eq_sq :
    (starRingEnd ℂ) (FormIndex.zeta 3) = FormIndex.zeta 3 ^ 2 := by
  have h3 : FormIndex.zeta 3 ^ 3 = 1 := FormIndex.zeta_pow_N (by norm_num)
  have hnorm : FormIndex.zeta 3 * (starRingEnd ℂ) (FormIndex.zeta 3) = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm]
    unfold FormIndex.zeta
    rw [Complex.norm_exp]
    norm_num
  calc (starRingEnd ℂ) (FormIndex.zeta 3)
      = (FormIndex.zeta 3 ^ 3) * (starRingEnd ℂ) (FormIndex.zeta 3) := by
        rw [h3, one_mul]
    _ = FormIndex.zeta 3 ^ 2
          * (FormIndex.zeta 3 * (starRingEnd ℂ) (FormIndex.zeta 3)) := by ring
    _ = FormIndex.zeta 3 ^ 2 := by rw [hnorm, mul_one]

/-! ### Shift: every symFam witness sits in the `a = 0` phase fiber -/

lemma parity_add_two (m : ℕ) (n : ZMod (2 * m)) :
    Surface.parity m (n + 2) = Surface.parity m n := by
  rw [map_add]
  have h2 : Surface.parity m 2 = 0 := by
    have h : Surface.parity m 2 = (2 : ZMod 2) := map_ofNat _ 2
    rw [h]
    decide
  rw [h2, add_zero]

/-- The step-2 shift fixes every parity-built family. -/
lemma shiftE_uncurry_punc0_symFam (ε : ℂ) (f : ℂ → ℂ) :
    shiftE m (Surface.uncurryE m (punc0 3 (symFam m ε f)))
      = Surface.uncurryE m (punc0 3 (symFam m ε f)) := by
  funext p
  change punc0 3 (symFam m ε f) (p.1 + 2) p.2 = punc0 3 (symFam m ε f) p.1 p.2
  unfold punc0
  have hsym : symFam m ε f (p.1 + 2) = symFam m ε f p.1 := by
    funext w
    unfold symFam
    rw [parity_add_two]
  rw [hsym]

lemma mem_shift_fiber_zero (ε : ℂ) (f : ℂ → ℂ) :
    Surface.uncurryE m (punc0 3 (symFam m ε f))
      ∈ Module.End.eigenspace (shiftE m) (FormIndex.zeta m ^ (0 : ℕ)) := by
  rw [Module.End.mem_eigenspace_iff, pow_zero, one_smul]
  exact shiftE_uncurry_punc0_symFam ε f

/-! ### Rotation: the generic eigenvector wrapper and the three characters -/

/-- A profile-level rotation eigenvalue lifts through `punc0 ∘ symFam`. -/
lemma rotE_eig_of_profile (ε μ : ℂ) {f : ℂ → ℂ}
    (hf : ∀ w, f (((rotUnit 3 : Circle) : ℂ) * w) = μ * f w) :
    rotE m ((rotUnit 3 : Circle) : ℂ)
        (Surface.uncurryE m (punc0 3 (symFam m ε f)))
      = μ • Surface.uncurryE m (punc0 3 (symFam m ε f)) := by
  funext p
  change punc0 3 (symFam m ε f) p.1 (((rotUnit 3 : Circle) : ℂ) * p.2)
      = μ * punc0 3 (symFam m ε f) p.1 p.2
  unfold punc0
  by_cases hA : p.2 ∈ Surface.punctures 3
  · rw [Set.indicator_of_notMem (by
        simp only [Set.mem_compl_iff, not_not]
        exact (rotUnit_mem_punctures_iff p.2).mpr hA),
      Set.indicator_of_notMem (by
        simp only [Set.mem_compl_iff, not_not]
        exact hA),
      mul_zero]
  · rw [Set.indicator_of_mem (by
        simp only [Set.mem_compl_iff]
        exact fun h => hA ((rotUnit_mem_punctures_iff p.2).mp h)),
      Set.indicator_of_mem (by
        simp only [Set.mem_compl_iff]
        exact hA)]
    unfold symFam cutD
    rw [rotUnit_norm_mul]
    split_ifs with hle
    · rw [hf]
      ring
    · ring

/-- `nu3` is rotation-invariant (norm-only). -/
lemma nu3_rot (w : ℂ) :
    nu3 3 (((rotUnit 3 : Circle) : ℂ) * w) = 1 * nu3 3 w := by
  unfold JacobiFields.nu3
  rw [rotUnit_norm_mul, one_mul]

/-- The `Jplus` profile is `2w²/D`: `nu1 + i·nu2` assembles the complex square. -/
lemma nuPlus_eq (z : ℂ) :
    nu1 3 z + Complex.I * nu2 3 z
      = 2 * z ^ 2 / ((‖z‖ ^ 4 + 1 : ℝ) : ℂ) := by
  unfold JacobiFields.nu1 JacobiFields.nu2
  have hz := Complex.re_add_im (z ^ 2)
  rw [show (2 * 3 - 2 : ℕ) = 4 by norm_num, show (3 - 1 : ℕ) = 2 by norm_num]
  push_cast
  rw [← mul_div_assoc, ← add_div]
  congr 1
  linear_combination (2 : ℂ) * hz

/-- The `Jminus` profile is `2·conj(w²)/D`. -/
lemma nuMinus_eq (z : ℂ) :
    nu1 3 z - Complex.I * nu2 3 z
      = 2 * (starRingEnd ℂ) (z ^ 2) / ((‖z‖ ^ 4 + 1 : ℝ) : ℂ) := by
  unfold JacobiFields.nu1 JacobiFields.nu2
  have hz : ((z ^ 2).re : ℂ) - ((z ^ 2).im : ℂ) * Complex.I
      = (starRingEnd ℂ) (z ^ 2) := by
    generalize z ^ 2 = w
    rw [Complex.ext_iff]
    constructor <;> simp
  rw [show (2 * 3 - 2 : ℕ) = 4 by norm_num, show (3 - 1 : ℕ) = 2 by norm_num]
  push_cast
  rw [← mul_div_assoc, ← sub_div]
  congr 1
  linear_combination (2 : ℂ) * hz

lemma nuPlus_rot (w : ℂ) :
    nu1 3 (((rotUnit 3 : Circle) : ℂ) * w)
        + Complex.I * nu2 3 (((rotUnit 3 : Circle) : ℂ) * w)
      = FormIndex.zeta 3 * (nu1 3 w + Complex.I * nu2 3 w) := by
  rw [nuPlus_eq, nuPlus_eq, rotUnit_norm_mul, mul_pow, rotUnit_sq]
  ring

lemma nuMinus_rot (w : ℂ) :
    nu1 3 (((rotUnit 3 : Circle) : ℂ) * w)
        - Complex.I * nu2 3 (((rotUnit 3 : Circle) : ℂ) * w)
      = FormIndex.zeta 3 ^ 2 * (nu1 3 w - Complex.I * nu2 3 w) := by
  rw [nuMinus_eq, nuMinus_eq, rotUnit_norm_mul, mul_pow, rotUnit_sq, map_mul,
    conj_zeta_eq_sq]
  ring

/-! ### The combination values -/

lemma Jplus_val : (Jplus m).val
    = punc0 3 (symFam m 1 fun w => nu1 3 w + Complex.I * nu2 3 w) := by
  change punc0 3 (symFam m 1 (nu1 3)) + Complex.I • punc0 3 (symFam m 1 (nu2 3)) = _
  funext n w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  unfold punc0
  by_cases hA : w ∈ (Surface.punctures 3)ᶜ
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA, Set.indicator_of_mem hA]
    unfold symFam cutD
    split_ifs with hle
    · ring
    · ring
  · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA,
      Set.indicator_of_notMem hA]
    ring

lemma Jminus_val : (Jminus m).val
    = punc0 3 (symFam m 1 fun w => nu1 3 w - Complex.I * nu2 3 w) := by
  change punc0 3 (symFam m 1 (nu1 3)) - Complex.I • punc0 3 (symFam m 1 (nu2 3)) = _
  funext n w
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  unfold punc0
  by_cases hA : w ∈ (Surface.punctures 3)ᶜ
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA, Set.indicator_of_mem hA]
    unfold symFam cutD
    split_ifs with hle
    · ring
    · ring
  · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA,
      Set.indicator_of_notMem hA]
    ring

/-! ### Eigenspace memberships and nonvanishing -/

theorem uncurry_J3_mem_shift :
    Surface.uncurryE m (J3 3 m (by norm_num)).val
      ∈ Module.End.eigenspace (shiftE m) (FormIndex.zeta m ^ (0 : ℕ)) :=
  mem_shift_fiber_zero _ _

theorem uncurry_Jplus_mem_shift :
    Surface.uncurryE m (Jplus m).val
      ∈ Module.End.eigenspace (shiftE m) (FormIndex.zeta m ^ (0 : ℕ)) := by
  rw [Jplus_val]
  exact mem_shift_fiber_zero _ _

theorem uncurry_Jminus_mem_shift :
    Surface.uncurryE m (Jminus m).val
      ∈ Module.End.eigenspace (shiftE m) (FormIndex.zeta m ^ (0 : ℕ)) := by
  rw [Jminus_val]
  exact mem_shift_fiber_zero _ _

theorem uncurry_J3_mem_rot :
    Surface.uncurryE m (J3 3 m (by norm_num)).val
      ∈ Module.End.eigenspace (rotE m ((rotUnit 3 : Circle) : ℂ))
          (FormIndex.zeta 3 ^ (0 : ℕ)) := by
  rw [Module.End.mem_eigenspace_iff, pow_zero, one_smul]
  have h := rotE_eig_of_profile (m := m) (-1) 1 nu3_rot
  rwa [one_smul] at h

theorem uncurry_Jplus_mem_rot :
    Surface.uncurryE m (Jplus m).val
      ∈ Module.End.eigenspace (rotE m ((rotUnit 3 : Circle) : ℂ))
          (FormIndex.zeta 3 ^ (1 : ℕ)) := by
  rw [Module.End.mem_eigenspace_iff, pow_one, Jplus_val]
  exact rotE_eig_of_profile 1 (FormIndex.zeta 3) nuPlus_rot

theorem uncurry_Jminus_mem_rot :
    Surface.uncurryE m (Jminus m).val
      ∈ Module.End.eigenspace (rotE m ((rotUnit 3 : Circle) : ℂ))
          (FormIndex.zeta 3 ^ (2 : ℕ)) := by
  rw [Module.End.mem_eigenspace_iff, Jminus_val]
  exact rotE_eig_of_profile 1 (FormIndex.zeta 3 ^ 2) nuMinus_rot

theorem Jplus_ne_zero : Jplus m ≠ 0 := by
  intro h
  have hli := linearIndependent_transJ 3 m (by norm_num)
  rw [Fintype.linearIndependent_iff] at hli
  have hsum : ∑ i, (![1, Complex.I, 0] : Fin 3 → ℂ) i
      • transJ 3 m (by norm_num) i = 0 := by
    simp only [transJ, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, one_smul, zero_smul, add_zero]
    exact h
  have := hli _ hsum 0
  simp at this

theorem Jminus_ne_zero : Jminus m ≠ 0 := by
  intro h
  have hli := linearIndependent_transJ 3 m (by norm_num)
  rw [Fintype.linearIndependent_iff] at hli
  have hsum : ∑ i, (![1, -Complex.I, 0] : Fin 3 → ℂ) i
      • transJ 3 m (by norm_num) i = 0 := by
    have hexp : ∑ i, (![1, -Complex.I, 0] : Fin 3 → ℂ) i
        • transJ 3 m (by norm_num) i = Jminus m := by
      simp only [transJ, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons, one_smul, zero_smul, add_zero]
      unfold Jminus
      module
    rw [hexp, h]
  have := hli _ hsum 0
  simp at this

theorem J3_ne_zero : J3 3 m (by norm_num) ≠ 0 := by
  intro h
  have hli := linearIndependent_transJ 3 m (by norm_num)
  rw [Fintype.linearIndependent_iff] at hli
  have hsum : ∑ i, (![0, 0, 1] : Fin 3 → ℂ) i
      • transJ 3 m (by norm_num) i = 0 := by
    simp only [transJ, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, one_smul, zero_smul, zero_add]
    exact h
  have := hli _ hsum 2
  simp at this

end KsIndex.JacobiFamily
