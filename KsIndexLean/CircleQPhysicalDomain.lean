module

public import KsIndexLean.CircleQPhysicalGraph

@[expose] public section


/-! Reconstruction of every admissible positive-lattice graph-domain trace. -/
noncomputable section
namespace KsIndex.CircleQ
open CircleSobolev PaperSlitAdapter SectorReduce Sector Trace

/-- Every trace in the physical positive-lattice domain comes from coefficient
membership, with equality in the half-order space itself. -/
theorem exists_physical_reconstruction (f : Space (1 / 2 : ℝ))
    (hf : MemDomSigma f) (hp : f ∈ character (1 / 2 : ℝ) (-1) 6) :
    ∃ (w : ℤ → ℂ) (hw : MemDom w),
      (traceOfSector (iotaTan 0 w) (iotaTan_mem_Domς 0 hw).1).val = f := by
  have hsupport := (mem_character _ _ _ _).mp hp
  have hz : coeff (1 / 2 : ℝ) f 0 = 0 := hsupport 0 (by
    rintro ⟨m, hm⟩; omega)
  let t : dotted (1 / 2 : ℝ) := ⟨f, hz⟩
  have hcs : ∀ l : ℤ, l % 3 ≠ 1 → coeff (1 / 2 : ℝ) t.val l = 0 := by
    intro l hl
    exact hsupport l (by rintro ⟨m, hm⟩; omega)
  have hv : sectorOfTrace t ∈ Domς :=
    (memDomSigma_iff_sectorOfTrace_mem_Domς t hcs).mp hf
  let w := restrictL (sectorOfTrace t)
  have hw : MemDom w := restrictL_memDom hv
  have he : iotaTan 0 w = sectorOfTrace t := by
    funext i
    cases i with
    | inl n => rfl
    | inr m =>
      rw [iotaTan_inr, sectorOfTrace_inr]
      have hzero : coeff (1 / 2 : ℝ) f (6 * m + 4) = 0 :=
        hsupport _ (by rintro ⟨n, hn⟩; omega)
      simp [coefT, t, hzero]
  refine ⟨w, hw, ?_⟩
  have hr := congrArg Subtype.val (traceOfSector_sectorOfTrace t hcs)
  simpa only [he] using hr

/-- The realization covers all physical test functions in the positive domain. -/
theorem exists_physicalTrace (f : Space (1 / 2 : ℝ))
    (hf : MemDomSigma f) (hp : f ∈ character (1 / 2 : ℝ) (-1) 6) :
    ∃ (w : ℤ → ℂ) (hw : MemDom w),
      physicalTrace w hw = toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2) f := by
  obtain ⟨w, hw, he⟩ := exists_physical_reconstruction f hf hp
  exact ⟨w, hw, congrArg (toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2)) he⟩

/-- Reconstruction also respects the actual graph-domain carrier. -/
theorem exists_physicalGraph (f : Space (1 / 2 : ℝ))
    (hf : MemDomSigma f) (hp : f ∈ character (1 / 2 : ℝ) (-1) 6) :
    ∃ (w : ℤ → ℂ) (hw : MemDom w), physicalGraph w hw = domPair f hf := by
  obtain ⟨w, hw, he⟩ := exists_physical_reconstruction f hf hp
  refine ⟨w, hw, ?_⟩
  unfold physicalGraph
  cases he
  rfl

end KsIndex.CircleQ
