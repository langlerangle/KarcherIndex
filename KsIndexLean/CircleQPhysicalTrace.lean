module

public import KsIndexLean.CircleQPhysicalMass
public import KsIndexLean.PaperSlitIndexTransport
public import KsIndexLean.SectorReduce

@[expose] public section


/-! Physical circle traces of the positive Fourier-lattice coefficient domain. -/
noncomputable section
open MeasureTheory
namespace KsIndex.CircleQ
open CircleSobolev PaperSlitAdapter SectorReduce Trace

/-- Realize a coefficient-domain vector on the frequencies `6n+1`. -/
def physicalTrace (w : ℤ → ℂ) (hw : MemDom w) : Lp ℂ 2 circleMeasure :=
  toL2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (traceOfSector (iotaTan 0 w) (Sector.mem_Domς.mp (iotaTan_mem_Domς 0 hw)).1).val

@[simp] theorem physicalTrace_fourier_lattice (w : ℤ → ℂ) (hw : MemDom w) (n : ℤ) :
    circleFourierCoeff (physicalTrace w hw) (6 * n + 1) = w n := by
  rw [physicalTrace, fourierCoeff_toL2, coeff_traceOfSector]
  change sectorInsertCoeff (iotaTan 0 w) (idxToℤ (Sum.inl n)) = w n
  rw [sectorInsertCoeff_lattice, iotaTan_inl]

/-- All Fourier coefficients outside the positive lattice vanish. -/
theorem physicalTrace_fourier_off (w : ℤ → ℂ) (hw : MemDom w) (l : ℤ)
    (hl : ¬ ∃ n : ℤ, 6 * n + 1 = l) :
    circleFourierCoeff (physicalTrace w hw) l = 0 := by
  rw [physicalTrace, fourierCoeff_toL2, coeff_traceOfSector]
  by_cases h : ∃ i, idxToℤ i = l
  · obtain ⟨i, rfl⟩ := h
    rw [sectorInsertCoeff_lattice]
    cases i with
    | inl n => exact False.elim (hl ⟨n, rfl⟩)
    | inr m => simp [iotaTan_inr, coefT]
  · exact sectorInsertCoeff_off _ l h

/-- The physical L² mass is `2π` times the coefficient mass. -/
theorem physicalTrace_mass (u v : ℤ → ℂ) (hu : MemDom u) (hv : MemDom v) :
    Statements.massPair u v = ((2 * Real.pi)⁻¹ : ℝ) •
      inner ℂ (physicalTrace u hu) (physicalTrace v hv) := by
  rw [← coefficient_massPair_eq_normalized_inner]
  have hinj : Function.Injective (fun n : ℤ => 6 * n + 1) := by
    intro a b h
    change 6 * a + 1 = 6 * b + 1 at h
    omega
  have he := hinj.tsum_eq (f := fun l =>
      starRingEnd ℂ (circleFourierCoeff (physicalTrace u hu) l) *
        circleFourierCoeff (physicalTrace v hv) l) (by
    intro l hl
    by_contra h
    have hz := physicalTrace_fourier_off u hu l h
    exact hl (by simp [hz]))
  simpa only [physicalTrace_fourier_lattice, Statements.massPair] using he

end KsIndex.CircleQ
