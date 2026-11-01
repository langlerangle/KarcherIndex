module

/-
Slit-to-sector index and nullity for the conjugate character.

The transport theorems assume `sin (απ) ≠ 0`.

The two rotation classes `c ≡ 1, 2 (mod 3)` are related by complex conjugation.  The direct
case `j ≡ 2` (PaperSlitIndexPIN) is transported to `j ≡ 1` across the conjugate-linear
equivalence `conjSlitEquiv α : paperSlitCharacterDomain α 1 ≃ₛₗ[starRingEnd ℂ]
paperSlitCharacterDomain (-α) 2` (ComplexH1ConjugationSlit), using the weak-Jacobi form
covariance `weakJacobi_conjH1` (ComplexH1ConjugationForm) as the quadratic/sesquilinear
intertwiner and the semilinear congruences `negativeIndex_congr_conj` / `sesqNullity_congr_conj`
(ConjTransfer).  The slit phase transforms `exp(2πiα) ↦ exp(-2πiα)`, so the sector target is at
parameter `-α`, as determined by the conjugated seam relation.

  paperSlit_pairWeakIndex_eq_sector_conj : pairWeakIndex (paperSlitCharacterDomain α 1)
      (surfacePotential 3) = formIndex (NQform (-α)) Domς                     (j ≡ 1)
  paperSlit_nullity_eq_sector_conj : sesqNullity Bpair = formNullity (NBform (-α)) Domς   (j ≡ 1)

Together with the direct character case, these identify both nontrivial
character counts with sector counts. The final wrappers use sector parity to
express the result at the original parameter `α`.
-/
public import KsIndexLean.PaperSlitIndexPIN
public import KsIndexLean.ComplexH1ConjugationForm
public import KsIndexLean.ComplexH1ConjugationSlit
public import KsIndexLean.ConjTransfer

@[expose] public section


noncomputable section
open scoped Real
open MeasureTheory
namespace KsIndex.PaperSlitAdapter
open KsIndex.Trace KsIndex.Sector KsIndex.CircleSobolev KsIndex.FormIndex KsIndex.WeakH1
  KsIndex.CircleQ KsIndex.Spectral KsIndex.NegativeDensity KsIndex.DtnBridge KsIndex.SectorForm

variable {α : ℝ}

lemma sin_neg_mul_pi_ne (hsin : Real.sin (α * Real.pi) ≠ 0) :
    Real.sin ((-α) * Real.pi) ≠ 0 := by
  rw [neg_mul, Real.sin_neg]; exact neg_ne_zero.mpr hsin

/-- **Conjugate-character index comparison.**  The pair weak index on `paperSlitCharacterDomain α 1`
equals the sector form index `formIndex (NQform (-α)) Domς`, transported from the direct case
`j ≡ 2` at parameter `-α` across the complex-conjugation equivalence `conjSlitEquiv`. -/
theorem paperSlit_pairWeakIndex_eq_sector_conj (hsin : Real.sin (α * Real.pi) ≠ 0) :
    pairWeakIndex (paperSlitCharacterDomain α 1) (surfacePotential 3)
      = formIndex (NQform (-α)) Domς := by
  have hj2 : pairWeakIndex (paperSlitCharacterDomain (-α) 2) (surfacePotential 3)
      = formIndex (NQform (-α)) Domς :=
    paperSlit_pairWeakIndex_eq_sector (by norm_num) (by norm_num) (by norm_num)
      (sin_neg_mul_pi_ne hsin)
  rw [pairWeakIndex_eq_pair_negativeIndex] at hj2 ⊢
  rw [← hj2]
  refine (negativeIndex_congr_conj (conjSlitEquiv α)
    (fun u : paperSlitCharacterDomain α 1 =>
      (weakJacobi (surfacePotential 3) u.val.1 u.val.1
        + weakJacobi (surfacePotential 3) u.val.2 u.val.2).re)
    (fun u : paperSlitCharacterDomain (-α) 2 =>
      (weakJacobi (surfacePotential 3) u.val.1 u.val.1
        + weakJacobi (surfacePotential 3) u.val.2 u.val.2).re)
    (fun u => ?_)).symm
  change (weakJacobi (surfacePotential 3) (conjH1 u.val.1) (conjH1 u.val.1)
      + weakJacobi (surfacePotential 3) (conjH1 u.val.2) (conjH1 u.val.2)).re
    = (weakJacobi (surfacePotential 3) u.val.1 u.val.1
      + weakJacobi (surfacePotential 3) u.val.2 u.val.2).re
  rw [weakJacobi_conjH1, weakJacobi_conjH1, ← map_add, Complex.conj_re]

/-- **Conjugate-character nullity comparison.**  The pair weak-Jacobi sesquilinear nullity on
`paperSlitCharacterDomain α 1` equals the sector form nullity `formNullity (NBform (-α)) Domς`. -/
theorem paperSlit_nullity_eq_sector_conj (hsin : Real.sin (α * Real.pi) ≠ 0) :
    sesqNullity (Bpair : paperSlitCharacterDomain α 1 → paperSlitCharacterDomain α 1 → ℂ)
      = formNullity (NBform (-α)) Domς := by
  have hj2 : sesqNullity
      (Bpair : paperSlitCharacterDomain (-α) 2 → paperSlitCharacterDomain (-α) 2 → ℂ)
      = formNullity (NBform (-α)) Domς :=
    paperSlit_nullity_eq_sector (by norm_num) (by norm_num) (by norm_num)
      (sin_neg_mul_pi_ne hsin)
  rw [← hj2]
  refine (sesqNullity_congr_conj (conjSlitEquiv α) Bpair Bpair (fun x y => ?_)).symm
  change weakJacobi (surfacePotential 3) (conjH1 x.val.1) (conjH1 y.val.1)
      + weakJacobi (surfacePotential 3) (conjH1 x.val.2) (conjH1 y.val.2)
    = (starRingEnd ℂ) (weakJacobi (surfacePotential 3) x.val.1 y.val.1
      + weakJacobi (surfacePotential 3) x.val.2 y.val.2)
  rw [weakJacobi_conjH1, weakJacobi_conjH1, map_add]

/-! ### Phase-sign symmetry and comparison at the original phase

The conjugate transport lands at parameter `-α`. The parity automorphism of
`Domς` identifies the sector forms at opposite parameters, so their index and
nullity agree. This sector comparison holds for every real `α`; composing it
with the slit transport retains the latter's nonzero-sine hypothesis. -/

/-- `M_{-α} = M_α†` (from `cos(-x)=cos x`, `sin(-x)=-sin x`). -/
lemma mulA_neg_eq_mulAdag (α : ℝ) (u : Idx → ℂ) : mulA (-α) u = mulAdag α u := by
  simp only [mulA, mulAdag, neg_mul, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg,
    mul_neg, neg_smul, sub_neg_eq_add]

/-- **Phase-sign symmetry of `NQform`:** the parity conjugates `α ↦ -α`. -/
lemma NQform_neg_parity (α : ℝ) (u : Idx → ℂ) : NQform (-α) (parity u) = NQform α u := by
  rw [NQform, NQform, Ndiag_parity, mulA_neg_eq_mulAdag, mulAdag_parity, Ndiag_parity]

/-- **Phase-sign symmetry of `NBform`:** the parity conjugates `α ↦ -α`. -/
lemma NBform_neg_parity (α : ℝ) (u v : Idx → ℂ) :
    NBform (-α) (parity u) (parity v) = NBform α u v := by
  rw [NBform, NBform, bN3_parity, mulA_neg_eq_mulAdag, mulA_neg_eq_mulAdag, mulAdag_parity,
    mulAdag_parity, bN3_parity]

/-- The parity as a `ℂ`-linear automorphism of the sector domain `Domς`. -/
def parityDomς : Domς ≃ₗ[ℂ] Domς where
  toFun u := ⟨parity u.val, parity_mem_Domς u.property⟩
  invFun u := ⟨parity u.val, parity_mem_Domς u.property⟩
  left_inv u := Subtype.ext (parity_involutive u.val)
  right_inv u := Subtype.ext (parity_involutive u.val)
  map_add' u v := Subtype.ext (parity_add u.val v.val)
  map_smul' c u := Subtype.ext (parity_smul c u.val)

/-- **Sector index phase-sign symmetry:** `formIndex (NQform (-α)) Domς = formIndex (NQform α) Domς`
(the count is invariant under `α ↦ -α`, via the parity automorphism of `Domς`). -/
lemma formIndex_NQform_neg_eq (α : ℝ) :
    formIndex (NQform (-α)) Domς = formIndex (NQform α) Domς := by
  rw [formIndex_NQform_Domς, formIndex_NQform_Domς]
  exact negativeIndex_congr parityDomς (fun x : Domς => NQform α x.val)
    (fun x : Domς => NQform (-α) x.val) (fun x => NQform_neg_parity α x.val)

/-- **Sector nullity phase-sign symmetry.** -/
lemma formNullity_NBform_neg_eq (α : ℝ) :
    formNullity (NBform (-α)) Domς = formNullity (NBform α) Domς := by
  rw [formNullity_NBform_Domς, formNullity_NBform_Domς]
  exact sesqNullity_congr parityDomς (fun u v : Domς => NBform α u.val v.val)
    (fun u v : Domς => NBform (-α) u.val v.val) (fun u v => NBform_neg_parity α u.val v.val)

/-- The `j = 1` slit-pair index equals the sector index at the original parameter `α`,
by conjugate transport followed by sector parity. -/
theorem paperSlit_pairWeakIndex_eq_sector_conj_alpha (hsin : Real.sin (α * Real.pi) ≠ 0) :
    pairWeakIndex (paperSlitCharacterDomain α 1) (surfacePotential 3)
      = formIndex (NQform α) Domς := by
  rw [paperSlit_pairWeakIndex_eq_sector_conj hsin, formIndex_NQform_neg_eq]

/-- The `j = 1` slit-pair nullity equals the sector nullity at the original parameter `α`. -/
theorem paperSlit_nullity_eq_sector_conj_alpha (hsin : Real.sin (α * Real.pi) ≠ 0) :
    sesqNullity (Bpair : paperSlitCharacterDomain α 1 → paperSlitCharacterDomain α 1 → ℂ)
      = formNullity (NBform α) Domς := by
  rw [paperSlit_nullity_eq_sector_conj hsin, formNullity_NBform_neg_eq]

end KsIndex.PaperSlitAdapter
