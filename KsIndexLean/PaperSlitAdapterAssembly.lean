module

/-
KsIndexLean — Disk-pair index coordinates and the k = 3 slit seam identity.

The first theorem identifies `pairWeakIndex` on its finite-Hilbert carrier with
`negativeIndex` of the sum of the two disk Jacobi forms. The remaining theorems
extract the two arc conditions and rotation characters from a slit-domain pair,
then identify the boundary coefficients of its upper trace with
`e^{iπα} • mulA α` applied to those of its lower trace, for `j % 3 = 2`.

These forward identities hold for every real phase. Reconstruction and the
nonintegral-phase splitting are supplied by `PaperSlitIndexTransport`; index
and nullity transport are assembled in `PaperSlitIndexPIN` and its conjugate
character companion.
-/
public import KsIndexLean.PaperSlitSectorAdapter
public import KsIndexLean.SlitReflectionIndex
public import KsIndexLean.PaperSlitSectorConnection

@[expose] public section


noncomputable section
open KsIndex.Spectral KsIndex.WeakH1 KsIndex.Trace KsIndex.NegativeDensity KsIndex.Sector

namespace KsIndex.PaperSlitAdapter

/-! ### The pair-wrapper bridge — `pairWeakIndex` ↔ the raw two-hemisphere `negativeIndex` -/

/-- `pairWeakIndex` on the finite-Hilbert carrier equals the raw `negativeIndex`
of the two-hemisphere `weakJacobi` sum on `D`.

The proof first instantiates `negativeIndex_linearEquiv` with the raw target
form, then unfolds the wrapper identities. This avoids unfolding the heavier
`finiteH1Domain` form during equivalence type inference. -/
lemma pairWeakIndex_eq_pair_negativeIndex (D : Submodule ℂ DiskPairH1)
    (V : BoundedRealPotential) :
    pairWeakIndex D V = negativeIndex (fun u : D =>
      (weakJacobi V u.val.1 u.val.1 + weakJacobi V u.val.2 u.val.2).re) := by
  have hz : weakJacobi V 0 0 = 0 := by
    have h := weakJacobi_add_left V 0 0 0
    simp only [add_zero] at h
    linear_combination -h
  have h := negativeIndex_linearEquiv (pairHilbertCoordinates D)
    (fun u : D => (weakJacobi V u.val.1 u.val.1 + weakJacobi V u.val.2 u.val.2).re)
    (by change (weakJacobi V 0 0 + weakJacobi V 0 0).re = 0
        simp only [hz, add_zero, Complex.zero_re])
  simpa only [pairWeakIndex, pairFiniteJacobi_eq] using h

/-! ### The seam and sector multiplier

The convention is fixed by `Surface.arc`: arc1 is `{cos 3θ > 0}` with phase 1,
and arc0 is `{cos 3θ < 0}` with phase `e^{2πiα}`. The square wave is +1 on arc1
and −1 on arc0; `mulA α = cos(απ)·I − i sin(απ)·ς`. The full-circle relation is
upper trace = `e^{iπα} • mulA α` applied to the lower trace. The norm-one scalar
cancels in the form pairing but remains in trace identities.

The Fourier support of the square wave lies at three times odd integers, so
multiplication exchanges the residue classes `6n+1` and `6m+4`. The physical
coefficient identity is supplied by `PaperSlitSectorConnection` and is composed
below with the extracted arc conditions and character support. -/

/-- **Seam extraction.** Membership in `paperSlitCharacterDomain α j` unpacks
(via its `paperSlitDomain` factor `= slitTraceDomain 3 (exp 2παi)`) to the two physical arc
conditions: equal boundary trace on the welded arc1, and the `exp(2παi)` phase jump on arc0. -/
lemma paperSlitCharacter_seam {α : ℝ} {j : ℕ} (u : paperSlitCharacterDomain α j) :
    arcTrace (boundaryArc 3 1) u.val.1 = arcTrace (boundaryArc 3 1) u.val.2 ∧
    arcTrace (boundaryArc 3 0) u.val.1
      = Complex.exp ((2 * Real.pi * α) * Complex.I) • arcTrace (boundaryArc 3 0) u.val.2 := by
  have hmem : u.val ∈ paperSlitDomain α := (Submodule.mem_inf.mp u.property).1
  rw [paperSlitDomain] at hmem
  exact (mem_slitTraceDomain 3 _ u.val).mp hmem

/-- **Character extraction.** The other `⊓` factor gives each hemisphere as a
`diskRotation(-2π/3)`-eigenvector with eigenvalue `zeta 3 ^ j` — restricting its Fourier
support to the class `ℓ ≡ -j (mod 3)`. -/
lemma paperSlitCharacter_character {α : ℝ} {j : ℕ} (u : paperSlitCharacterDomain α j) :
    u.val.1 ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j) ∧
    u.val.2 ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j) := by
  have hmem : u.val ∈ pairCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j) :=
    (Submodule.mem_inf.mp u.property).2
  exact (mem_pairCharacterDomain_iff _ _ u.val).mp hmem

/-! ### The forward seam identity on the sector coefficients

Compose arc gluing (`seam_full_relation`), character support and
`seam_coeff_eq_mulA`. The direct case has `j % 3 = 2`. The conjugate character
case uses complex conjugation, which also changes the phase from `α` to `-α`. -/

/-- **Class support (direct case `j≡2`).**  The second-hemisphere trace of a
`paperSlitCharacterDomain α j` element has Fourier support in the class `{d%3=1}` when `j≡2 (mod 3)`
(`trace_character` + `boundaryRotation_eigen_iff_support`). -/
lemma paperSlitCharacter_class_support {α : ℝ} {j : ℕ} (hj : j % 3 = 2)
    (u : paperSlitCharacterDomain α j) :
    ∀ d : ℤ, d % 3 ≠ 1 → circleFourierCoeff (diskTraceCLM u.val.2) d = 0 := by
  have hrot' : boundaryRotation (-(2 * Real.pi) / 3) (diskTraceCLM u.val.2)
      = KsIndex.FormIndex.zeta 3 ^ (j : ℤ) • diskTraceCLM u.val.2 := by
    rw [zpow_natCast]; exact trace_character (paperSlitCharacter_character u).2
  have hsupp := (boundaryRotation_eigen_iff_support 3 (by norm_num) (j : ℤ)
    (diskTraceCLM u.val.2)).mp hrot'
  intro d hd
  apply hsupp
  rintro ⟨m, hm⟩
  omega

/-- **Forward seam→`mulA` for the paper-slit pair (direct case `j≡2`).**  Composes seam extraction,
arc-gluing, class support, and the coefficient intertwiner: the sector coefficients of hemisphere
1's boundary trace are `e^{iπα}·mulA α` of hemisphere 2's. -/
theorem paperSlit_seam_coeff_eq_mulA {α : ℝ} {j : ℕ} (hj : j % 3 = 2)
    (u : paperSlitCharacterDomain α j) :
    (fun i : Idx => circleFourierCoeff (diskTraceCLM u.val.1) (idxToNZ i).val)
      = Complex.exp (Complex.I * (α * Real.pi)) •
          mulA α (fun i : Idx => circleFourierCoeff (diskTraceCLM u.val.2) (idxToNZ i).val) := by
  have hseam := paperSlitCharacter_seam u
  exact seam_coeff_eq_mulA α (diskTraceCLM u.val.1) (diskTraceCLM u.val.2)
    (seam_full_relation α u.val.1 u.val.2 hseam.1 hseam.2)
    (paperSlitCharacter_class_support hj u)

end KsIndex.PaperSlitAdapter
