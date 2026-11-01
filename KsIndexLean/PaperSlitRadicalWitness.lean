module

/-
Weak radical witnesses with recovered hemisphere traces.

For `sin (απ) ≠ 0`, a vector `φ` in the radical of `NBform α` on `Domς`
lifts to `u := (Ψ …).symm (φ, 0, 0)`. The zero remainder components and the
block-form identity show that `Bpair u w = 0` for every test pair `w`.
The construction also recovers the lower trace as `φ.val` and the upper
trace data as `exp (I * (απ)) • mulA α φ.val`.

These statements construct weak `H¹` witness data in the direct character
class `j = 2`; they do not assert boundedness or a smooth representative.
The general theorem accepts a pair with the specified `Ψ` image, while the
`_symm` theorem supplies that pair explicitly using the inverse equivalence.
-/
public import KsIndexLean.PaperSlitIndexPIN

@[expose] public section

noncomputable section
open scoped Real
open MeasureTheory
namespace KsIndex.PaperSlitAdapter
open KsIndex.Trace KsIndex.Sector KsIndex.CircleSobolev KsIndex.FormIndex KsIndex.WeakH1
  KsIndex.CircleQ KsIndex.Spectral KsIndex.NegativeDensity KsIndex.DtnBridge KsIndex.SectorForm

variable {α : ℝ}

/-- **Radical witness (direct `j = 2`), general form.**  If a disk pair `u ∈
paperSlitCharacterDomain α 2` maps under `Ψ` to `(φ, 0, 0)` (sector data `φ`, zero character
remainder) and `φ` is a sector radical vector of `NBform α` on `Domς`, then:
* `u` is a pair weak-Jacobi radical vector (`∀ w, Bpair u w = 0`) — weak Jacobi-field data;
* lower-trace recovery: `sectorTrace u.val.2 = φ`;
* upper-trace recovery: the hemisphere-1 sector data is `e^{iπα}·mulA α φ` (the seam-gluing /
  covering-coordinate matching, at coefficient level on the `Domς` lattice).
The witness itself is `u := (Ψ …).symm (φ, 0, 0)` (see `paperSlit_radical_witness_symm`). -/
theorem paperSlit_radical_witness (hj0 : (0 : ℕ) < 2) (hjk : (2 : ℕ) < 3) (hj : (2 : ℕ) % 3 = 2)
    (hsin : Real.sin (α * Real.pi) ≠ 0) (φ : Domς)
    (hrad : ∀ ψ : Domς, NBform α φ.val ψ.val = 0)
    (u : paperSlitCharacterDomain α 2) (hu : Ψ hj0 hjk hj hsin u = (φ, 0, 0)) :
    (∀ w : paperSlitCharacterDomain α 2, Bpair u w = 0)
      ∧ sectorTrace u.val.2 = φ.val
      ∧ sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character u).1)
          = Complex.exp (Complex.I * (α * Real.pi)) • mulA α φ.val := by
  have hlow : sectorTrace u.val.2 = φ.val := by
    have hf := Ψ_apply_fst hj0 hjk hj hsin u
    rw [hu] at hf
    exact hf.symm
  refine ⟨fun w => ?_, hlow, ?_⟩
  · have hb := NBsplitForm_Ψ hj0 hjk hj hsin u w
    rw [← hb, hu]
    simp only [NBsplitB, ZeroMemClass.coe_zero, weakJacobi_zero_left3, add_zero]
    rw [hrad (Ψ hj0 hjk hj hsin w).1]
    ring
  · have hseam : sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character u).1)
        = Complex.exp (Complex.I * (α * Real.pi)) •
            mulA α (sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character u).2)) := by
      rw [sectorOfTrace_charTrace_eq hj0 hjk (paperSlitCharacter_character u).1,
        sectorOfTrace_charTrace_eq hj0 hjk (paperSlitCharacter_character u).2]
      exact paperSlit_seam_coeff_eq_mulA hj u
    rw [hseam, ← sectorTrace_eq_sectorOfTrace hj0 hjk (paperSlitCharacter_character u).2, hlow]

/-- **Radical witness (direct `j = 2`), the explicit `Ψ.symm` construction.** -/
theorem paperSlit_radical_witness_symm (hj0 : (0 : ℕ) < 2) (hjk : (2 : ℕ) < 3)
    (hj : (2 : ℕ) % 3 = 2) (hsin : Real.sin (α * Real.pi) ≠ 0) (φ : Domς)
    (hrad : ∀ ψ : Domς, NBform α φ.val ψ.val = 0) :
    (∀ w : paperSlitCharacterDomain α 2,
        Bpair ((Ψ hj0 hjk hj hsin).symm (φ, 0, 0)) w = 0)
      ∧ sectorTrace (((Ψ hj0 hjk hj hsin).symm (φ, 0, 0)).val.2) = φ.val
      ∧ sectorOfTrace (charTrace hj0 hjk
          (paperSlitCharacter_character ((Ψ hj0 hjk hj hsin).symm (φ, 0, 0))).1)
          = Complex.exp (Complex.I * (α * Real.pi)) • mulA α φ.val :=
  paperSlit_radical_witness hj0 hjk hj hsin φ hrad _ ((Ψ hj0 hjk hj hsin).apply_symm_apply _)

end KsIndex.PaperSlitAdapter
