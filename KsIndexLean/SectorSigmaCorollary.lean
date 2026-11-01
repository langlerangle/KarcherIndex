module

public import KsIndexLean.CircleSigmaDomain
public import KsIndexLean.PaperSlitIndexTransport

@[expose] public section


/-! # Identification of the circle graph domain with the sector domain

For a dotted half-order trace supported on frequencies congruent to `1`
modulo `3`, `memDomSigma_iff_sectorOfTrace_mem_Domς` identifies membership
in the sign-multiplier graph domain with membership of its coefficient
restriction in `Sector.Domς`. The two sector lattices are `6n+1` and `6m+4`.

Conversely, `memDomSigma_traceOfSector` reconstructs a graph-domain function
from every sector-domain vector. The trace reconstruction and restriction
round trips give the two-sided domain identification.

The proof uses the Fourier intertwining of the sign multiplier with the
sector half-swap, together with `|ℓ| ≤ 1+|ℓ| ≤ 2|ℓ|` on the nonzero class
lattice. This comparison proves equivalence of the summability conditions;
it does not assert equality of the two weighted norms.
-/

noncomputable section
open MeasureTheory
namespace KsIndex.PaperSlitAdapter
open KsIndex.Trace KsIndex.Sector KsIndex.CircleSobolev

/-- Class support transfers from stored coefficients to the `L²` realization. -/
lemma toL2Half_class_support (f : dotted (1 / 2 : ℝ))
    (hf : ∀ ℓ : ℤ, ℓ % 3 ≠ 1 → coeff (1 / 2 : ℝ) f.val ℓ = 0) :
    ∀ d : ℤ, d % 3 ≠ 1 → circleFourierCoeff (toL2Half f.val) d = 0 := by
  intro d hd
  rw [fourierCoeff_toL2]
  exact hf d hd

/-- The sector trace of `σ·f` is the sector half-swap of the sector trace of `f`
(the `sectorConnection` intertwining, read on traces). -/
lemma sectorOfTrace_sigmaMul (f : dotted (1 / 2 : ℝ))
    (hf : ∀ ℓ : ℤ, ℓ % 3 ≠ 1 → coeff (1 / 2 : ℝ) f.val ℓ = 0) :
    (fun i : Idx => circleFourierCoeff (sigmaMul (toL2Half f.val)) (idxToℤ i))
      = sgn (sectorOfTrace f) := by
  have hconn := sectorConnection (toL2Half f.val) (toL2Half_class_support f hf)
  have hcoeff : (fun i : Idx => circleFourierCoeff (toL2Half f.val) (idxToNZ i).val)
      = sectorOfTrace f := by
    funext i
    cases i with
    | inl n =>
        rw [idxToNZ_inl_val, fourierCoeff_toL2, sectorOfTrace_inl]
    | inr m =>
        rw [idxToNZ_inr_val, fourierCoeff_toL2, sectorOfTrace_inr]
  calc (fun i : Idx => circleFourierCoeff (sigmaMul (toL2Half f.val)) (idxToℤ i))
      = fun i : Idx => circleFourierCoeff (sigmaMul (toL2Half f.val)) (idxToNZ i).val := rfl
    _ = sgn (fun i : Idx => circleFourierCoeff (toL2Half f.val) (idxToNZ i).val) := hconn
    _ = sgn (sectorOfTrace f) := by rw [hcoeff]

/-- For class-supported coefficient data, the circle `H^{1/2}` weight condition is
equivalent to sector membership of the class restriction (`|ℓ| ≤ 1+|ℓ| ≤ 2|ℓ|` on the
class). -/
lemma summable_weighted_iff_memSector {g : ℤ → ℂ}
    (hg : ∀ ℓ : ℤ, ℓ % 3 ≠ 1 → g ℓ = 0) :
    Summable (fun ℓ : ℤ => (1 + |(ℓ : ℝ)|) * ‖g ℓ‖ ^ 2)
      ↔ MemSector (fun i : Idx => g (idxToℤ i)) := by
  constructor
  · intro hs
    constructor
    · have hinj : Function.Injective (fun n : ℤ => (6 * n + 1 : ℤ)) := by
        intro a b h
        simp only at h
        omega
      refine ((hs.comp_injective hinj).of_nonneg_of_le (fun n => by positivity)
        (fun n => ?_))
      simp only [Function.comp, idxToℤ_inl]
      rw [show ((6 * n + 1 : ℤ) : ℝ) = 6 * (n : ℝ) + 1 by push_cast; ring]
      exact mul_le_mul_of_nonneg_right
        (by linarith [abs_nonneg (6 * (n : ℝ) + 1)]) (sq_nonneg _)
    · have hinj : Function.Injective (fun m : ℤ => (6 * m + 4 : ℤ)) := by
        intro a b h
        simp only at h
        omega
      refine ((hs.comp_injective hinj).of_nonneg_of_le (fun m => by positivity)
        (fun m => ?_))
      simp only [Function.comp, idxToℤ_inr]
      rw [show ((6 * m + 4 : ℤ) : ℝ) = 6 * (m : ℝ) + 4 by push_cast; ring]
      exact mul_le_mul_of_nonneg_right
        (by linarith [abs_nonneg (6 * (m : ℝ) + 4)]) (sq_nonneg _)
  · intro hv
    have hins := sectorInsert_summable hv
    have hw (m : ℤ) : weight (1 / 2 : ℝ) m ^ 2 = 1 + |(m : ℝ)| := by
      rw [weight_sq]
      norm_num
    refine hins.congr (fun ℓ => ?_)
    have hcoeff : sectorInsertCoeff (fun i : Idx => g (idxToℤ i)) ℓ = g ℓ := by
      by_cases hm : ∃ i, idxToℤ i = ℓ
      · obtain ⟨i, rfl⟩ := hm
        rw [sectorInsertCoeff_lattice]
      · rw [sectorInsertCoeff_off _ ℓ hm,
          hg ℓ (fun h1 => hm ((idxToℤ_mem_range_iff ℓ).mpr h1))]
    rw [hw, hcoeff]

/-- A dotted class-supported trace lies in the circle sign-multiplier graph
 domain exactly when its sector trace belongs to `Sector.Domς`. -/
theorem memDomSigma_iff_sectorOfTrace_mem_Domς (f : dotted (1 / 2 : ℝ))
    (hf : ∀ ℓ : ℤ, ℓ % 3 ≠ 1 → coeff (1 / 2 : ℝ) f.val ℓ = 0) :
    MemDomSigma f.val ↔ sectorOfTrace f ∈ Domς := by
  have hGclass : ∀ d : ℤ, d % 3 ≠ 1
      → circleFourierCoeff (sigmaMul (toL2Half f.val)) d = 0 :=
    sigmaMul_class_support (toL2Half f.val) (toL2Half_class_support f hf)
  have hbridge := summable_weighted_iff_memSector hGclass
  rw [mem_Domς]
  constructor
  · intro hmem
    refine ⟨memSector_sectorOfTrace f, ?_⟩
    rw [← sectorOfTrace_sigmaMul f hf]
    apply hbridge.mp
    rw [MemDomSigma, mem_range_toL2_iff] at hmem
    rw [show (2 * (1 / 2 : ℝ)) = 1 by norm_num] at hmem
    simpa only [Real.rpow_one] using hmem
  · rintro ⟨-, hsgn⟩
    rw [← sectorOfTrace_sigmaMul f hf] at hsgn
    rw [MemDomSigma, mem_range_toL2_iff]
    rw [show (2 * (1 / 2 : ℝ)) = 1 by norm_num]
    simpa only [Real.rpow_one] using hbridge.mpr hsgn

/-- **The converse realization**: every element of the audited `Sector.Domς` realizes a
function in the paper's `H^{1/2}_ς(S¹)` through the shelf reconstruction
`traceOfSector` (with the round-trips this closes the two-sided identification). -/
theorem memDomSigma_traceOfSector {v : Idx → ℂ} (hv : v ∈ Domς) :
    MemDomSigma (traceOfSector v hv.1).val := by
  have hcs := traceOfSector_class_support v hv.1
  rw [memDomSigma_iff_sectorOfTrace_mem_Domς _ hcs, sectorOfTrace_traceOfSector]
  exact hv

end KsIndex.PaperSlitAdapter
