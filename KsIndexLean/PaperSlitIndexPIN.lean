module

/-
# Slit-to-sector index and nullity transport

For `0 < j < 3`, `j % 3 = 2`, and `sin (απ) ≠ 0`, the equivalence `Ψ`
splits the slit pair into its second-hemisphere sector trace and two zero-trace
Dirichlet remainders. The quadratic and sesquilinear forms split accordingly.
Nonnegativity of the remainders preserves the negative index; strict positivity
removes their contribution to the nullity. The factor `2π` is positive and does
not change either count.

`paperSlit_pairWeakIndex_eq_sector` and `paperSlit_nullity_eq_sector` give the
two resulting equalities. The conjugate character case is treated in
`PaperSlitIndexPINConj`, with the phase changed to `-α` before the subsequent
same-phase sector comparison. Local irreducibility keeps the equivalence and
transported forms opaque during elaboration.
-/
public import KsIndexLean.PaperSlitIndexTransport
public import KsIndexLean.PositiveBlockCounts

@[expose] public section


noncomputable section
open scoped Real
open MeasureTheory
namespace KsIndex.PaperSlitAdapter
open KsIndex.Trace KsIndex.Sector KsIndex.CircleSobolev KsIndex.FormIndex KsIndex.WeakH1
  KsIndex.CircleQ KsIndex.Spectral KsIndex.NegativeDensity KsIndex.DtnBridge KsIndex.SectorForm

set_option maxHeartbeats 2000000

variable {α : ℝ} {j : ℕ}

/-- `charRem j` is the paper's full zero-trace Dirichlet character block. -/
lemma charRem_eq_mixed (j : ℕ) : charRem j = mixedCharacterDomain 3 j false false := by
  rw [mixedDD_eq_fullDirichletCharacter (by norm_num) j, charRem]
  norm_num

/-- Weak-Jacobi self-energy of a `charRem` element is nonnegative. -/
lemma charRem_weakJacobi_nonneg (hj0 : 0 < j) (hjk : j < 3) {r : ComplexH1}
    (hr : r ∈ charRem j) : 0 ≤ (weakJacobi (surfacePotential 3) r r).re := by
  rcases eq_or_ne r 0 with h0 | h0
  · subst h0
    have h := weakJacobi_add_left (surfacePotential 3) 0 0 0
    simp only [add_zero] at h
    have : weakJacobi (surfacePotential 3) 0 0 = 0 := by linear_combination -h
    rw [this, Complex.zero_re]
  · have hm : r ∈ mixedCharacterDomain 3 j false false := by rw [← charRem_eq_mixed]; exact hr
    have hne : (⟨r, hm⟩ : mixedCharacterDomain 3 j false false) ≠ 0 := by
      simp only [ne_eq, Submodule.mk_eq_zero]; exact h0
    exact (generalDirichlet_character_positive_of_range (by norm_num) hj0 hjk ⟨r, hm⟩ hne).le

/-- The sector target form on the codomain of `Ψ`: `2π·NQform` plus the remainder self-energies. -/
def QsplitForm (α : ℝ) (p : Domς × charRem j × charRem j) : ℝ :=
  2 * Real.pi * NQform α p.1.val
    + ((weakJacobi (surfacePotential 3) p.2.1.val p.2.1.val).re
        + (weakJacobi (surfacePotential 3) p.2.2.val p.2.2.val).re)

/-- The pair weak-Jacobi energy (the `pairWeakIndex` integrand). -/
def Qpair (u : paperSlitCharacterDomain α j) : ℝ :=
  (weakJacobi (surfacePotential 3) u.val.1 u.val.1
    + weakJacobi (surfacePotential 3) u.val.2 u.val.2).re

/-- The first component of `Ψ` is the second hemisphere's sector trace. -/
lemma Ψ_apply_fst (hj0 : 0 < j) (hjk : j < 3) (hj : j % 3 = 2)
    (hsin : Real.sin (α * Real.pi) ≠ 0) (u : paperSlitCharacterDomain α j) :
    (Ψ hj0 hjk hj hsin u).1.val = sectorTrace u.val.2 := rfl

lemma Ψ_apply_rem1 (hj0 : 0 < j) (hjk : j < 3) (hj : j % 3 = 2)
    (hsin : Real.sin (α * Real.pi) ≠ 0) (u : paperSlitCharacterDomain α j) :
    (Ψ hj0 hjk hj hsin u).2.1.val = u.val.1 - jacobiExtensionCLM (show 2 ≤ 3 by norm_num)
      (charTrace hj0 hjk (paperSlitCharacter_character u).1) := rfl

lemma Ψ_apply_rem2 (hj0 : 0 < j) (hjk : j < 3) (hj : j % 3 = 2)
    (hsin : Real.sin (α * Real.pi) ≠ 0) (u : paperSlitCharacterDomain α j) :
    (Ψ hj0 hjk hj hsin u).2.2.val = u.val.2 - jacobiExtensionCLM (show 2 ≤ 3 by norm_num)
      (charTrace hj0 hjk (paperSlitCharacter_character u).2) := rfl

/-- **Forward block form.**  Along `Ψ`, the pair weak-Jacobi energy equals `2π·NQform α` on the
hemisphere-2 sector trace plus the two zero-trace remainder self-energies. -/
lemma QsplitForm_Ψ (hj0 : 0 < j) (hjk : j < 3) (hj : j % 3 = 2)
    (hsin : Real.sin (α * Real.pi) ≠ 0) (u : paperSlitCharacterDomain α j) :
    QsplitForm α (Ψ hj0 hjk hj hsin u) = Qpair u := by
  have hb1 := charHemi_block hj0 hjk (paperSlitCharacter_character u).1
  have hb2 := charHemi_block hj0 hjk (paperSlitCharacter_character u).2
  rw [faithfulDtnB_self_eq_Ndiag _
    (charTrace_class_support hj0 hjk hj (paperSlitCharacter_character u).1)] at hb1
  rw [faithfulDtnB_self_eq_Ndiag _
    (charTrace_class_support hj0 hjk hj (paperSlitCharacter_character u).2)] at hb2
  have hbd := boundary_eq_NQform hj0 hjk hj u
  have hst := sectorTrace_eq_sectorOfTrace hj0 hjk (paperSlitCharacter_character u).2
  rw [QsplitForm, Qpair, Ψ_apply_fst, Ψ_apply_rem1, Ψ_apply_rem2, hst, Complex.add_re,
    hb1, hb2]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, mul_zero, sub_zero, zero_mul, add_zero, Complex.re_ofNat,
    Complex.im_ofNat]
  rw [← hbd]
  ring

/-- `weakJacobi` vanishes at the origin. -/
lemma weakJacobi_zero_zero : weakJacobi (surfacePotential 3) 0 0 = 0 := by
  have h := weakJacobi_add_left (surfacePotential 3) 0 0 0
  simp only [add_zero] at h; linear_combination -h

/-! ### Negative index transport -/

attribute [local irreducible] Ψ Qpair QsplitForm

set_option maxHeartbeats 200000 in
/-- **Direct-character index comparison.**  The pair weak-Jacobi negative index on `paperSlitCharacterDomain α j`
equals the sector form index `formIndex (NQform α) Domς` — for `j≡2 (mod 3)`, `sin πα ≠ 0`. -/
theorem paperSlit_index_eq_sector (hj0 : 0 < j) (hjk : j < 3) (hj : j % 3 = 2)
    (hsin : Real.sin (α * Real.pi) ≠ 0) :
    negativeIndex (Qpair : paperSlitCharacterDomain α j → ℝ) = formIndex (NQform α) Domς := by
  have hwz := weakJacobi_zero_zero
  have hQ0 : (fun w : Domς => 2 * Real.pi * NQform α w.val) 0 = 0 := by
    show 2 * Real.pi * NQform α (0 : Domς).val = 0
    rw [show ((0 : Domς).val) = (0 : Idx → ℂ) from rfl, NQform_zero, mul_zero]
  have hR0 : (fun rr : charRem j × charRem j =>
      (weakJacobi (surfacePotential 3) rr.1.val rr.1.val).re
        + (weakJacobi (surfacePotential 3) rr.2.val rr.2.val).re) 0 = 0 := by
    show (weakJacobi (surfacePotential 3) (0 : charRem j).val (0 : charRem j).val).re
        + (weakJacobi (surfacePotential 3) (0 : charRem j).val (0 : charRem j).val).re = 0
    rw [show ((0 : charRem j).val) = (0 : ComplexH1) from rfl, hwz, Complex.zero_re, add_zero]
  have hRp : ∀ y : charRem j × charRem j,
      0 ≤ (weakJacobi (surfacePotential 3) y.1.val y.1.val).re
        + (weakJacobi (surfacePotential 3) y.2.val y.2.val).re := fun y =>
    add_nonneg (charRem_weakJacobi_nonneg hj0 hjk y.1.property)
      (charRem_weakJacobi_nonneg hj0 hjk y.2.property)
  -- Transport the index along `Ψ`.
  -- Keep the split form symbolic during elaboration.
  have hQ0split : QsplitForm α (0 : Domς × charRem j × charRem j) = 0 := by
    simp only [QsplitForm, Prod.fst_zero, Prod.snd_zero, ZeroMemClass.coe_zero, NQform_zero,
      weakJacobi_zero_zero, Complex.zero_re, mul_zero, add_zero]
  have hle : negativeIndex (Qpair : paperSlitCharacterDomain α j → ℝ)
      = negativeIndex (QsplitForm α : Domς × charRem j × charRem j → ℝ) :=
    (negativeIndex_congr (Ψ hj0 hjk hj hsin) Qpair (QsplitForm α)
      (QsplitForm_Ψ hj0 hjk hj hsin)).symm
  calc negativeIndex (Qpair : paperSlitCharacterDomain α j → ℝ)
      = negativeIndex (QsplitForm α) := hle
    _ = negativeIndex (fun w : Domς => 2 * Real.pi * NQform α w.val) := by
        unfold QsplitForm
        exact negativeIndex_nonnegative_product (fun w : Domς => 2 * Real.pi * NQform α w.val)
          (fun rr : charRem j × charRem j =>
            (weakJacobi (surfacePotential 3) rr.1.val rr.1.val).re
              + (weakJacobi (surfacePotential 3) rr.2.val rr.2.val).re) hQ0 hR0 hRp
    _ = negativeIndex (fun w : Domς => NQform α w.val) :=
        negativeIndex_pos_mul (fun w : Domς => NQform α w.val) (2 * Real.pi) Real.two_pi_pos
    _ = formIndex (NQform α) Domς := (formIndex_NQform_Domς α).symm

attribute [local semireducible] Qpair QsplitForm

/-- The slit-pair weak index equals the sector index under the direct-character hypotheses. -/
theorem paperSlit_pairWeakIndex_eq_sector (hj0 : 0 < j) (hjk : j < 3) (hj : j % 3 = 2)
    (hsin : Real.sin (α * Real.pi) ≠ 0) :
    pairWeakIndex (paperSlitCharacterDomain α j) (surfacePotential 3)
      = formIndex (NQform α) Domς := by
  rw [pairWeakIndex_eq_pair_negativeIndex]
  exact paperSlit_index_eq_sector hj0 hjk hj hsin

/-! ### Sesquilinear boundary identity

The nullity transport uses the sesquilinear form identity below, strict positivity
of the Dirichlet remainder, and invariance under nonzero scalar multiplication. -/

/-- `conj(e^{iπα})·e^{iπα} = 1` (unimodularity in the sesquilinear form). -/
lemma expInPi_conj_mul_self (α : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * (α * Real.pi)))
      * Complex.exp (Complex.I * (α * Real.pi)) = 1 := by
  have hz : (starRingEnd ℂ) (Complex.I * (α * Real.pi)) = -(Complex.I * (α * Real.pi)) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  rw [← Complex.exp_conj, hz, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

set_option maxHeartbeats 1000000 in
/-- **Boundary form = `NBform` (sesquilinear).**  The two-hemisphere boundary `bN3` pairing equals
`NBform α` on hemisphere-2's sector coefficients — the sesquilinear analogue of
`boundary_eq_NQform`, via the seam↔`mulA` on both arguments and the conjugate-unimodular invariance
of `bN3`. -/
lemma boundary_eq_NBform (hj0 : 0 < j) (hjk : j < 3) (hj : j % 3 = 2)
    (u v : paperSlitCharacterDomain α j) :
    bN3 (sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character u).1))
          (sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character v).1))
        + bN3 (sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character u).2))
          (sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character v).2))
      = NBform α (sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character u).2))
          (sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character v).2)) := by
  have hσ1u : sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character u).1)
      = Complex.exp (Complex.I * (α * Real.pi))
          • mulA α (sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character u).2)) := by
    rw [sectorOfTrace_charTrace_eq hj0 hjk (paperSlitCharacter_character u).1,
      sectorOfTrace_charTrace_eq hj0 hjk (paperSlitCharacter_character u).2]
    exact paperSlit_seam_coeff_eq_mulA hj u
  have hσ1v : sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character v).1)
      = Complex.exp (Complex.I * (α * Real.pi))
          • mulA α (sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character v).2)) := by
    rw [sectorOfTrace_charTrace_eq hj0 hjk (paperSlitCharacter_character v).1,
      sectorOfTrace_charTrace_eq hj0 hjk (paperSlitCharacter_character v).2]
    exact paperSlit_seam_coeff_eq_mulA hj v
  rw [hσ1u, hσ1v, bN3_smul_left, bN3_smul_right, ← mul_assoc, expInPi_conj_mul_self, one_mul,
    NBform]
  ring


/-! ### Sesquilinear nullity transport -/

lemma charHemi_block_sesq (hj0 : 0 < j) (hjk : j < 3) {x y : ComplexH1}
    (hx : x ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j))
    (hy : y ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) :
    weakJacobi (surfacePotential 3) x y
      = (2 * Real.pi : ℂ) * faithfulDtnB 3 (charTrace hj0 hjk hx) (charTrace hj0 hjk hy)
        + weakJacobi (surfacePotential 3)
            (x - jacobiExtensionCLM (show 2 ≤ 3 by norm_num) (charTrace hj0 hjk hx))
            (y - jacobiExtensionCLM (show 2 ≤ 3 by norm_num) (charTrace hj0 hjk hy)) := by
  have hzx := (Submodule.mem_inf.mp (charHemi_remainder_mem hj0 hjk hx)).1
  have hzy := (Submodule.mem_inf.mp (charHemi_remainder_mem hj0 hjk hy)).1
  have hb := jacobiExtensionCLM_block_form (show 2 ≤ 3 by norm_num)
    (charTrace hj0 hjk hx) (charTrace hj0 hjk hy)
    (x - jacobiExtensionCLM (show 2 ≤ 3 by norm_num) (charTrace hj0 hjk hx))
    (y - jacobiExtensionCLM (show 2 ≤ 3 by norm_num) (charTrace hj0 hjk hy)) hzx hzy
  rwa [show jacobiExtensionCLM (show 2 ≤ 3 by norm_num) (charTrace hj0 hjk hx)
        + (x - jacobiExtensionCLM (show 2 ≤ 3 by norm_num) (charTrace hj0 hjk hx)) = x from by abel,
    show jacobiExtensionCLM (show 2 ≤ 3 by norm_num) (charTrace hj0 hjk hy)
        + (y - jacobiExtensionCLM (show 2 ≤ 3 by norm_num) (charTrace hj0 hjk hy)) = y from by abel]
    at hb

/-- The pair weak-Jacobi sesquilinear form used in the nullity transport. -/
def Bpair (u v : paperSlitCharacterDomain α j) : ℂ :=
  weakJacobi (surfacePotential 3) u.val.1 v.val.1
    + weakJacobi (surfacePotential 3) u.val.2 v.val.2

/-- The sector target sesquilinear form on the codomain of `Ψ`. -/
def NBsplitB (α : ℝ) (p q : Domς × charRem j × charRem j) : ℂ :=
  (2 * Real.pi : ℂ) * NBform α p.1.val q.1.val
    + (weakJacobi (surfacePotential 3) p.2.1.val q.2.1.val
        + weakJacobi (surfacePotential 3) p.2.2.val q.2.2.val)


/-- **Forward sesquilinear block form.** -/
lemma NBsplitForm_Ψ (hj0 : 0 < j) (hjk : j < 3) (hj : j % 3 = 2)
    (hsin : Real.sin (α * Real.pi) ≠ 0) (u v : paperSlitCharacterDomain α j) :
    NBsplitB α (Ψ hj0 hjk hj hsin u) (Ψ hj0 hjk hj hsin v) = Bpair u v := by
  have hb1 := charHemi_block_sesq hj0 hjk (paperSlitCharacter_character u).1
    (paperSlitCharacter_character v).1
  have hb2 := charHemi_block_sesq hj0 hjk (paperSlitCharacter_character u).2
    (paperSlitCharacter_character v).2
  rw [← bN3_sectorOfTrace_eq_faithfulDtnB _ _
    (charTrace_class_support hj0 hjk hj (paperSlitCharacter_character v).1)] at hb1
  rw [← bN3_sectorOfTrace_eq_faithfulDtnB _ _
    (charTrace_class_support hj0 hjk hj (paperSlitCharacter_character v).2)] at hb2
  have hbd := boundary_eq_NBform hj0 hjk hj u v
  have hstu := sectorTrace_eq_sectorOfTrace hj0 hjk (paperSlitCharacter_character u).2
  have hstv := sectorTrace_eq_sectorOfTrace hj0 hjk (paperSlitCharacter_character v).2
  simp only [NBsplitB, Bpair, Ψ_apply_fst, Ψ_apply_rem1, Ψ_apply_rem2, hstu, hstv]
  rw [hb1, hb2, ← hbd]
  ring

/-- Strict positivity of the weak-Jacobi self-energy on a nonzero `charRem` element. -/
lemma charRem_weakJacobi_pos (hj0 : 0 < j) (hjk : j < 3) {r : ComplexH1}
    (hr : r ∈ charRem j) (hr0 : r ≠ 0) : 0 < (weakJacobi (surfacePotential 3) r r).re := by
  have hm : r ∈ mixedCharacterDomain 3 j false false := by rw [← charRem_eq_mixed]; exact hr
  have hne : (⟨r, hm⟩ : mixedCharacterDomain 3 j false false) ≠ 0 := by
    simp only [ne_eq, Submodule.mk_eq_zero]; exact hr0
  exact generalDirichlet_character_positive_of_range (by norm_num) hj0 hjk ⟨r, hm⟩ hne

/-- `weakJacobi` vanishes with a zero left argument. -/
lemma weakJacobi_zero_left3 (v : ComplexH1) : weakJacobi (surfacePotential 3) 0 v = 0 := by
  have h := weakJacobi_add_left (surfacePotential 3) 0 0 v
  simp only [add_zero] at h; linear_combination -h

/-- `NBform` vanishes with a zero right argument. -/
lemma NBform_zero_right3 (α : ℝ) (u : Idx → ℂ) : NBform α u 0 = 0 := by
  have h := NBform_smul_right α (0 : ℂ) u u
  rw [zero_smul, zero_mul] at h; exact h

attribute [local irreducible] Bpair NBsplitB

set_option maxHeartbeats 400000 in
/-- **Direct-character nullity comparison.**  The pair weak-Jacobi sesquilinear nullity on
`paperSlitCharacterDomain α j` equals the sector form nullity `formNullity (NBform α) Domς`. -/
theorem paperSlit_nullity_eq_sector (hj0 : 0 < j) (hjk : j < 3) (hj : j % 3 = 2)
    (hsin : Real.sin (α * Real.pi) ≠ 0) :
    sesqNullity (Bpair : paperSlitCharacterDomain α j → paperSlitCharacterDomain α j → ℂ)
      = formNullity (NBform α) Domς := by
  have hB0 : ∀ x : Domς, (fun w w' : Domς => (2 * Real.pi : ℂ) * NBform α w.val w'.val) x 0 = 0 :=
    fun x => by
      show (2 * Real.pi : ℂ) * NBform α x.val (0 : Domς).val = 0
      rw [show ((0 : Domς).val) = (0 : Idx → ℂ) from rfl, NBform_zero_right3, mul_zero]
  have hC0 : ∀ y : charRem j × charRem j,
      (fun rr rr' : charRem j × charRem j =>
        weakJacobi (surfacePotential 3) rr.1.val rr'.1.val
          + weakJacobi (surfacePotential 3) rr.2.val rr'.2.val) 0 y = 0 := fun y => by
    show weakJacobi (surfacePotential 3) (0 : charRem j).val y.1.val
        + weakJacobi (surfacePotential 3) (0 : charRem j).val y.2.val = 0
    rw [show ((0 : charRem j).val) = (0 : ComplexH1) from rfl, weakJacobi_zero_left3,
      weakJacobi_zero_left3, add_zero]
  have hpos : ∀ y : charRem j × charRem j, y ≠ 0 →
      0 < ((fun rr rr' : charRem j × charRem j =>
        weakJacobi (surfacePotential 3) rr.1.val rr'.1.val
          + weakJacobi (surfacePotential 3) rr.2.val rr'.2.val) y y).re := fun y hy => by
    simp only [Complex.add_re]
    rcases not_and_or.mp (fun h => hy (Prod.ext h.1 h.2)) with h1 | h2
    · exact add_pos_of_pos_of_nonneg
        (charRem_weakJacobi_pos hj0 hjk y.1.property (fun hc => h1 (Subtype.ext hc)))
        (charRem_weakJacobi_nonneg hj0 hjk y.2.property)
    · exact add_pos_of_nonneg_of_pos (charRem_weakJacobi_nonneg hj0 hjk y.1.property)
        (charRem_weakJacobi_pos hj0 hjk y.2.property (fun hc => h2 (Subtype.ext hc)))
  have hcongr := sesqNullity_congr (Ψ hj0 hjk hj hsin) Bpair (NBsplitB α)
    (NBsplitForm_Ψ hj0 hjk hj hsin)
  calc sesqNullity (Bpair : paperSlitCharacterDomain α j → paperSlitCharacterDomain α j → ℂ)
      = sesqNullity (NBsplitB α) := hcongr.symm
    _ = sesqNullity (fun w w' : Domς => (2 * Real.pi : ℂ) * NBform α w.val w'.val) := by
        unfold NBsplitB
        exact sesqNullity_positive_product
          (fun w w' : Domς => (2 * Real.pi : ℂ) * NBform α w.val w'.val)
          (fun rr rr' : charRem j × charRem j =>
            weakJacobi (surfacePotential 3) rr.1.val rr'.1.val
              + weakJacobi (surfacePotential 3) rr.2.val rr'.2.val) hB0 hC0 hpos
    _ = sesqNullity (fun w w' : Domς => NBform α w.val w'.val) :=
        sesqNullity_nonzero_mul (fun w w' : Domς => NBform α w.val w'.val) (2 * Real.pi : ℂ)
          (by exact_mod_cast Real.two_pi_pos.ne')
    _ = formNullity (NBform α) Domς := (formNullity_NBform_Domς α).symm


end KsIndex.PaperSlitAdapter
