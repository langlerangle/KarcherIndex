module

/-
Index and nullity comparison for the two nontrivial slit rotation characters.

For an interior phase `0 < α < 1`, the real quadratic index and complex
sesquilinear nullity of the weak disk-pair form on `paperSlitCharacterDomain α j`
agree with the corresponding circle-sector invariants on `Domς`, provided
`j` is not divisible by three.

The character depends only on `j % 3`. The proof dispatches to the direct
class `j ≡ 2` and the conjugate class `j ≡ 1`, both with the same parameter `α`.
The interior-phase hypotheses supply `sin (α * π) ≠ 0` for the boundary
reconstruction. The trivial rotation character and endpoint phases are not
covered by these comparison theorems.

These are analytic disk-pair-to-circle comparisons. Their application to
geometric quotients uses the separate rational-phase slit correspondence.
-/
public import KsIndexLean.PaperSlitIndexPINConj

@[expose] public section


noncomputable section
open scoped Real
open MeasureTheory
namespace KsIndex.PaperSlitAdapter
open KsIndex.Trace KsIndex.Sector KsIndex.CircleSobolev KsIndex.FormIndex KsIndex.WeakH1
  KsIndex.CircleQ KsIndex.Spectral KsIndex.NegativeDensity KsIndex.DtnBridge KsIndex.SectorForm

variable {α : ℝ} {j : ℕ}

/-- The two nontrivial rotation characters, `j ≢ 0 (mod 3)`.
The trivial character is handled separately. -/
def SectorClass (j : ℕ) : Prop := ¬ (3 ∣ j)

/-- The character eigenvalue `zeta 3 ^ j` depends only on `j % 3` (since `zeta 3 ^ 3 = 1`). -/
lemma zeta3_pow_mod (j : ℕ) : (zeta 3) ^ j = (zeta 3) ^ (j % 3) := by
  conv_lhs => rw [← Nat.div_add_mod j 3]
  rw [pow_add, pow_mul, zeta_pow_N (by norm_num : (0 : ℕ) < 3), one_pow, one_mul]

/-- On the physical interior `0 < α < 1`, `sin(απ) ≠ 0`. -/
lemma sin_pi_ne_of_interior (h0 : 0 < α) (h1 : α < 1) : Real.sin (α * Real.pi) ≠ 0 := by
  have : 0 < Real.sin (α * Real.pi) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith [Real.pi_pos, Real.pi_gt_three]
  linarith

/-- The paper-slit character domain depends only on `j % 3`. -/
lemma paperSlitCharacterDomain_mod (α : ℝ) (j : ℕ) :
    paperSlitCharacterDomain α j = paperSlitCharacterDomain α (j % 3) := by
  unfold paperSlitCharacterDomain
  rw [zeta3_pow_mod]

/-- At interior phase, each nontrivial slit rotation character has the same
negative index as the circle-sector quadratic form at that phase. -/
theorem paperSlit_index_eq_sectorClass (α : ℝ) (h0 : 0 < α) (h1 : α < 1) (hj : SectorClass j) :
    negativeIndex (fun u : paperSlitCharacterDomain α j =>
        (weakJacobi (surfacePotential 3) u.val.1 u.val.1
       + weakJacobi (surfacePotential 3) u.val.2 u.val.2).re)
      = formIndex (NQform α) Domς := by
  have hsin := sin_pi_ne_of_interior h0 h1
  have hne : j % 3 ≠ 0 := fun h => hj (Nat.dvd_of_mod_eq_zero h)
  have hmod : j % 3 = 1 ∨ j % 3 = 2 := by omega
  rw [paperSlitCharacterDomain_mod]
  rcases hmod with h | h <;> rw [h]
  · rw [← pairWeakIndex_eq_pair_negativeIndex]
    exact paperSlit_pairWeakIndex_eq_sector_conj_alpha hsin
  · exact paperSlit_index_eq_sector (by norm_num) (by norm_num) (by norm_num) hsin

/-- At interior phase, each nontrivial slit rotation character has the same
sesquilinear nullity as the circle-sector form at that phase. -/
theorem paperSlit_nullity_eq_sectorClass (α : ℝ) (h0 : 0 < α) (h1 : α < 1) (hj : SectorClass j) :
    sesqNullity (fun u v : paperSlitCharacterDomain α j =>
        weakJacobi (surfacePotential 3) u.val.1 v.val.1
      + weakJacobi (surfacePotential 3) u.val.2 v.val.2)
      = formNullity (NBform α) Domς := by
  have hsin := sin_pi_ne_of_interior h0 h1
  have hne : j % 3 ≠ 0 := fun h => hj (Nat.dvd_of_mod_eq_zero h)
  have hmod : j % 3 = 1 ∨ j % 3 = 2 := by omega
  rw [paperSlitCharacterDomain_mod]
  rcases hmod with h | h <;> rw [h]
  · exact paperSlit_nullity_eq_sector_conj_alpha hsin
  · exact paperSlit_nullity_eq_sector (by norm_num) (by norm_num) (by norm_num) hsin

end KsIndex.PaperSlitAdapter
