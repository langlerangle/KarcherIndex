module

/-
# Boundary forms for slit pairs

The two hemisphere boundary energies reduce to `NQform α` on the sector
coefficients of the second trace, for `0 < j < 3` and `j % 3 = 2`.
The seam relation is `σt1 = exp (iπα) • mulA α σt2`: its unit-modulus scalar
cancels in the energy, but remains part of the trace equality.

`faithfulDtnB_self_eq_Ndiag` identifies the Dirichlet-to-Neumann self-pairing
with the coefficient energy. `boundary_eq_NQform` combines the two energies.
Under the additional hypothesis `sin (απ) ≠ 0`, solving the seam relation for
the sign-multiplied trace proves membership in `Domς`. These are the boundary
identities used by the slit-pair splitting and the index/nullity transport.
-/
public import KsIndexLean.PaperSlitAdapterAssembly
public import KsIndexLean.PaperSlitHemisphereSplit

@[expose] public section


noncomputable section
open scoped Real
open MeasureTheory
namespace KsIndex.PaperSlitAdapter
open KsIndex.Trace KsIndex.Sector KsIndex.SectorForm KsIndex.DtnBridge KsIndex.CircleSobolev
open KsIndex.FormIndex KsIndex.WeakH1

/-- `Ndiag` scales by `‖c‖²` under scalar multiplication. -/
lemma Ndiag_smul (c : ℂ) (u : Idx → ℂ) : Ndiag (c • u) = ‖c‖ ^ 2 * Ndiag u := by
  simp only [Ndiag, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [mul_add, ← tsum_mul_left, ← tsum_mul_left]
  congr 1 <;> exact tsum_congr fun _ => by ring

/-- `‖e^{iπα}‖ = 1` (the phase is unimodular). -/
lemma norm_expInPi (α : ℝ) : ‖Complex.exp (Complex.I * (α * Real.pi))‖ = 1 := by
  rw [Complex.norm_exp]; simp [Complex.mul_re]

/-- The faithful DtN self-energy of a class-supported trace is `Ndiag` of its
sector coefficients. -/
lemma faithfulDtnB_self_eq_Ndiag (t : dotted (1 / 2 : ℝ))
    (hcls : ∀ ℓ : ℤ, ℓ % 3 ≠ 1 → coeff (1 / 2 : ℝ) t.val ℓ = 0) :
    faithfulDtnB 3 t t = (Ndiag (sectorOfTrace t) : ℂ) := by
  rw [← bN3_sectorOfTrace_eq_faithfulDtnB t t hcls, bN3_self]

/-- The sector coefficients of a character hemisphere's trace are the `idxToNZ`-reindexed physical
Fourier coefficients — the object of `paperSlit_seam_coeff_eq_mulA`. -/
lemma sectorOfTrace_charTrace_eq {j : ℕ} (hj0 : 0 < j) (hjk : j < 3) {u : ComplexH1}
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) :
    sectorOfTrace (charTrace hj0 hjk hu)
      = fun i : Idx => circleFourierCoeff (diskTraceCLM u) (idxToNZ i).val := by
  funext i
  cases i with
  | inl n =>
      change coeff (1 / 2 : ℝ) (charTrace hj0 hjk hu).val (6 * n + 1)
        = circleFourierCoeff (diskTraceCLM u) (idxToNZ (Sum.inl n)).val
      rw [idxToNZ_inl_val]; exact coeff_halfDiskTrace u (6 * n + 1)
  | inr m =>
      change coeff (1 / 2 : ℝ) (charTrace hj0 hjk hu).val (6 * m + 4)
        = circleFourierCoeff (diskTraceCLM u) (idxToNZ (Sum.inr m)).val
      rw [idxToNZ_inr_val]; exact coeff_halfDiskTrace u (6 * m + 4)

/-- Disk-trace class support of any character hemisphere (`j≡2`). -/
lemma weakCharacter_diskTrace_class_support {j : ℕ} (hj : j % 3 = 2) {u : ComplexH1}
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) :
    ∀ d : ℤ, d % 3 ≠ 1 → circleFourierCoeff (diskTraceCLM u) d = 0 := by
  have hrot' : boundaryRotation (-(2 * Real.pi) / 3) (diskTraceCLM u)
      = KsIndex.FormIndex.zeta 3 ^ (j : ℤ) • diskTraceCLM u := by
    rw [zpow_natCast]; exact trace_character hu
  have hsupp := (boundaryRotation_eigen_iff_support 3 (by norm_num) (j : ℤ)
    (diskTraceCLM u)).mp hrot'
  intro d hd
  exact hsupp d (by rintro ⟨m, hm⟩; omega)

/-- `coeff (1/2)` class support of a character hemisphere's trace (`j≡2`). -/
lemma charTrace_class_support {j : ℕ} (hj0 : 0 < j) (hjk : j < 3) (hj : j % 3 = 2)
    {u : ComplexH1}
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) :
    ∀ ℓ : ℤ, ℓ % 3 ≠ 1 → coeff (1 / 2 : ℝ) (charTrace hj0 hjk hu).val ℓ = 0 := by
  intro ℓ hℓ
  change coeff (1 / 2 : ℝ) (halfDiskTraceCLM u) ℓ = 0
  rw [halfDiskTraceCLM_apply, coeff_halfDiskTrace]
  exact weakCharacter_diskTrace_class_support hj hu ℓ hℓ

/-- **Boundary form = `NQform`.**  The two-hemisphere boundary `Ndiag`-sum equals `NQform α` on
hemisphere 2's sector coefficients — via the seam↔`mulA` (`σt1 = e^{iπα}·mulA α σt2`) and the
unimodular invariance of `Ndiag`. -/
lemma boundary_eq_NQform {α : ℝ} {j : ℕ} (hj0 : 0 < j) (hjk : j < 3) (hj : j % 3 = 2)
    (u : paperSlitCharacterDomain α j) :
    Ndiag (sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character u).1))
      + Ndiag (sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character u).2))
      = NQform α (sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character u).2)) := by
  have hchar := paperSlitCharacter_character u
  have hσ1 : sectorOfTrace (charTrace hj0 hjk hchar.1)
      = Complex.exp (Complex.I * (α * Real.pi))
          • mulA α (sectorOfTrace (charTrace hj0 hjk hchar.2)) := by
    rw [sectorOfTrace_charTrace_eq hj0 hjk hchar.1, sectorOfTrace_charTrace_eq hj0 hjk hchar.2]
    exact paperSlit_seam_coeff_eq_mulA hj u
  rw [hσ1, Ndiag_smul, norm_expInPi, one_pow, one_mul, NQform]
  ring

/-- **Hhalf recovery — the `Domς` membership.**  For a paper-slit pair (`j≡2`, `sin πα ≠ 0`),
hemisphere 2's sector coefficients lie in `Domς`: `MemSector` is automatic; `MemSector (sgn ·)`
follows by solving the seam relation `σt1 = e^{iπα}·mulA α σt2` for `sgn σt2` — a linear combination
of the two hemispheres' (both `MemSector`) sector coefficients (`sin πα ≠ 0` for the interior
`0<α<1`).  This is the graph-domain recovery the pair splitting `Ψ` needs. -/
lemma sectorOfTrace_charTrace_mem_Domς {α : ℝ} {j : ℕ} (hj0 : 0 < j) (hjk : j < 3) (hj : j % 3 = 2)
    (hsin : Real.sin (α * Real.pi) ≠ 0)
    (u : paperSlitCharacterDomain α j) :
    sectorOfTrace (charTrace hj0 hjk (paperSlitCharacter_character u).2) ∈ Domς := by
  have hchar := paperSlitCharacter_character u
  set σt1 := sectorOfTrace (charTrace hj0 hjk hchar.1) with hσt1
  set σt2 := sectorOfTrace (charTrace hj0 hjk hchar.2) with hσt2
  have hσ1 : σt1 = Complex.exp (Complex.I * (α * Real.pi)) • mulA α σt2 := by
    rw [hσt1, hσt2, sectorOfTrace_charTrace_eq hj0 hjk hchar.1,
      sectorOfTrace_charTrace_eq hj0 hjk hchar.2]
    exact paperSlit_seam_coeff_eq_mulA hj u
  have hM1 : MemSector σt1 := hσt1 ▸ memSector_sectorOfTrace _
  have hM2 : MemSector σt2 := hσt2 ▸ memSector_sectorOfTrace _
  refine ⟨hM2, ?_⟩
  have hne : Complex.I * (Real.sin (α * Real.pi) : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hsin)
  have hexp : Complex.exp (-(Complex.I * (α * Real.pi)))
      * Complex.exp (Complex.I * (α * Real.pi)) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have e1 : Complex.exp (-(Complex.I * (α * Real.pi))) • σt1 = mulA α σt2 := by
    rw [hσ1, smul_smul, hexp, one_smul]
  have hlin : (Complex.I * (Real.sin (α * Real.pi) : ℂ)) • sgn σt2
      = (Real.cos (α * Real.pi) : ℂ) • σt2
        - Complex.exp (-(Complex.I * (α * Real.pi))) • σt1 := by
    rw [e1]; simp only [mulA]; abel
  have hsgn : sgn σt2
      = (Complex.I * (Real.sin (α * Real.pi) : ℂ))⁻¹
          • ((Real.cos (α * Real.pi) : ℂ) • σt2
            - Complex.exp (-(Complex.I * (α * Real.pi))) • σt1) :=
    (eq_inv_smul_iff₀ hne).mpr hlin
  have hcombo : ((Real.cos (α * Real.pi) : ℂ) • σt2
        - Complex.exp (-(Complex.I * (α * Real.pi))) • σt1)
      = (Real.cos (α * Real.pi) : ℂ) • σt2
        + (-Complex.exp (-(Complex.I * (α * Real.pi)))) • σt1 := by
    rw [neg_smul, sub_eq_add_neg]
  rw [hsgn, hcombo]
  exact memSector_smul _ (memSector_add (memSector_smul _ hM2) (memSector_smul _ hM1))

end KsIndex.PaperSlitAdapter
