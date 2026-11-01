module

public import KsIndexLean.CircleQPhysicalTrace
public import KsIndexLean.CircleQCoercivity
public import KsIndexLean.SectorSigmaCorollary

@[expose] public section


/-! Graph norms of reconstructed circle traces. -/
noncomputable section
namespace KsIndex.PaperSlitAdapter
open CircleSobolev Sector Trace

/-- The half-order norm of a reconstructed trace is the inhomogeneous lattice sum. -/
theorem traceOfSector_norm_sq (v : Idx → ℂ) (hv : MemSector v) :
    ‖(traceOfSector v hv).val‖ ^ 2 =
      ∑' i : Idx, (1 + |(idxToℤ i : ℝ)|) * ‖v i‖ ^ 2 := by
  have h := idxToℤ_injective.tsum_eq (f := fun l : ℤ =>
    weight (1 / 2 : ℝ) l ^ 2 * ‖sectorInsertCoeff v l‖ ^ 2) (by
      intro l hl
      by_contra hn
      exact hl (by simp [sectorInsertCoeff_off v l hn]))
  have hn := (hasSum_weighted_sq (1 / 2 : ℝ) (traceOfSector v hv).val).tsum_eq
  simp only [coeff_traceOfSector] at hn
  rw [← hn, ← h]
  apply tsum_congr
  intro i
  rw [sectorInsertCoeff_lattice, weight_sq]
  norm_num

/-- Sign multiplication of a reconstructed domain trace is reconstructed from
its sign-transformed sector coefficients, in the actual half-order space. -/
theorem sigmaLift_traceOfSector {v : Idx → ℂ} (hv : v ∈ Domς) :
    sigmaLift (traceOfSector v hv.1).val (memDomSigma_traceOfSector hv) =
      (traceOfSector (sgn v) hv.2).val := by
  symm
  apply sigmaLift_unique
  apply lp_ext_of_fourierCoeff
  intro l
  have hcs := traceOfSector_class_support v hv.1
  have hconn := sectorOfTrace_sigmaMul (traceOfSector v hv.1) hcs
  rw [sectorOfTrace_traceOfSector] at hconn
  by_cases hm : ∃ i, idxToℤ i = l
  · obtain ⟨i, rfl⟩ := hm
    rw [fourierCoeff_toL2, coeff_traceOfSector, sectorInsertCoeff_lattice]
    exact (congrFun hconn i).symm
  · rw [fourierCoeff_toL2, coeff_traceOfSector, sectorInsertCoeff_off _ l hm]
    symm
    exact sigmaMul_class_support _ (toL2Half_class_support _ hcs) l
      (fun h => hm ((idxToℤ_mem_range_iff l).mpr h))

/-- Split the reconstructed norm into its two frequency lattices. -/
theorem traceOfSector_norm_sq_split (v : Idx → ℂ) (hv : MemSector v) :
    ‖(traceOfSector v hv).val‖ ^ 2 =
      (∑' n : ℤ, (1 + |6 * (n : ℝ) + 1|) * ‖v (Sum.inl n)‖ ^ 2) +
      (∑' m : ℤ, (1 + |6 * (m : ℝ) + 4|) * ‖v (Sum.inr m)‖ ^ 2) := by
  have hs := (sectorInsert_summable hv).comp_injective idxToℤ_injective
  have hs' : Summable (fun i : Idx => (1 + |(idxToℤ i : ℝ)|) * ‖v i‖ ^ 2) := by
    apply hs.congr
    intro i
    simp [sectorInsertCoeff_lattice, weight_sq]
  rw [traceOfSector_norm_sq]
  have h := Summable.tsum_sum (f := fun i : Idx =>
    (1 + |(idxToℤ i : ℝ)|) * ‖v i‖ ^ 2)
    (hs'.comp_injective Sum.inl_injective) (hs'.comp_injective Sum.inr_injective)
  simpa only [idxToℤ_inl, idxToℤ_inr, Int.cast_add, Int.cast_mul,
    Int.cast_ofNat, Int.cast_one] using h

end KsIndex.PaperSlitAdapter

namespace KsIndex.CircleQ
open CircleSobolev PaperSlitAdapter SectorReduce Sector

/-- The graph-domain element corresponding to a coefficient-domain vector. -/
def physicalGraph (w : ℤ → ℂ) (hw : MemDom w) : ↥sigmaGraph :=
  domPair (traceOfSector (iotaTan 0 w) (iotaTan_mem_Domς 0 hw).1).val
    (memDomSigma_traceOfSector (iotaTan_mem_Domς 0 hw))

/-- Exact identification of the physical graph norm and the coefficient weights. -/
theorem physicalGraph_norm_sq (w : ℤ → ℂ) (hw : MemDom w) :
    ‖physicalGraph w hw‖ ^ 2 = coefficientGraphNormSq w := by
  rw [physicalGraph, domPair_norm_sq, sigmaLift_traceOfSector (iotaTan_mem_Domς 0 hw),
    traceOfSector_norm_sq_split, traceOfSector_norm_sq_split,
    sgn_iotaTan 0 (summable_normSq hw.1)]
  simp only [iotaTan_inl, iotaTan_inr, coefT, zero_mul, Real.sin_zero,
    Real.cos_zero, zero_div, Complex.ofReal_zero, mul_zero, norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, tsum_zero,
    add_zero, zero_add, Sum.elim_inl, Sum.elim_inr]
  simp_rw [add_mul, one_mul]
  rw [(summable_normSq hw.1).tsum_add hw.1,
    (SIsometry.summable_convS_sq (summable_normSq hw.1)).tsum_add hw.2,
    SIsometry.tsum_convS_sq_eq_normSq hw]
  unfold coefficientGraphNormSq normSq
  ring

/-- Coercivity measured in the actual sign-multiplier graph norm. -/
theorem physicalGraph_coercivity (s : ℝ) (w : ℤ → ℂ) (hw : MemDom w) :
    min 1 (s ^ 2) * ‖physicalGraph w hw‖ ^ 2 ≤
      Qform s w + 5 * (1 + s ^ 2) * normSq w := by
  rw [physicalGraph_norm_sq]
  exact coefficient_graph_coercivity s hw

end KsIndex.CircleQ
