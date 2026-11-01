module

public import KsIndexLean.CircleQPhysicalForm

@[expose] public section


/-! For positive parameters, the variational threshold is the least eigenvalue
of the physical circle form. -/
noncomputable section
namespace KsIndex.CircleQ
open CircleSobolev PaperSlitAdapter SectorReduce Sector Trace Statements

/-- Reconstructed coefficient vectors have the physical positive character. -/
theorem reconstructed_mem_positive (w : ℤ → ℂ) (hw : MemDom w) :
    (traceOfSector (iotaTan 0 w) (iotaTan_mem_Domς 0 hw).1).val ∈
      character (1 / 2 : ℝ) (-1) 6 := by
  rw [mem_character]
  intro l hl
  have hbad : ¬ ∃ n : ℤ, 6 * n + 1 = l := by
    rintro ⟨n, hn⟩
    exact hl ⟨n, by omega⟩
  have h := physicalTrace_fourier_off w hw l hbad
  simpa only [physicalTrace, fourierCoeff_toL2] using h

/-- A nonzero coefficient vector reconstructs to a nonzero half-order trace. -/
theorem reconstructed_ne_zero (w : ℤ → ℂ) (hw : MemDom w) (hne : w ≠ 0) :
    (traceOfSector (iotaTan 0 w) (iotaTan_mem_Domς 0 hw).1).val ≠ 0 := by
  intro hz
  apply hne
  funext n
  have h := congrArg (fun z : Space (1 / 2 : ℝ) =>
    coeff (1 / 2 : ℝ) z (idxToℤ (Sum.inl n))) hz
  rw [coeff_traceOfSector, sectorInsertCoeff_lattice, iotaTan_inl] at h
  simpa [coeff] using h

/-- A physical eigenvalue is defined by all admissible graph-domain tests and
the actual arclength L² inner product. -/
def IsPhysicalEigenvalue (s mu : ℝ) : Prop :=
  ∃ (f : Space (1 / 2 : ℝ)) (hf : MemDomSigma f),
    f ∈ character (1 / 2 : ℝ) (-1) 6 ∧ f ≠ 0 ∧
      ∀ (g : Space (1 / 2 : ℝ)) (hg : MemDomSigma g),
        g ∈ character (1 / 2 : ℝ) (-1) 6 →
          physicalForm s (domPair g hg) (domPair f hf) =
            inner ℂ (toL2Half g) ((mu : ℂ) • toL2Half f)

/-- For positive parameters, the attained coefficient infimum supplies a physical eigenvector. -/
theorem gam_isPhysicalEigenvalue {s : ℝ} (hs : 0 < s) :
    IsPhysicalEigenvalue s (gam s) := by
  obtain ⟨u, hu, _, hne, he⟩ := exists_least_coefficient_eigenvector hs
  refine ⟨_, memDomSigma_traceOfSector (iotaTan_mem_Domς 0 hu),
    reconstructed_mem_positive u hu, reconstructed_ne_zero u hu hne, ?_⟩
  intro g hg hp
  exact physicalForm_eigen_equation s (gam s) u hu he g hg hp

/-- Every physical eigenvalue is bounded below by the same variational infimum. -/
theorem gam_le_physicalEigenvalue {s mu : ℝ} (he : IsPhysicalEigenvalue s mu) :
    gam s ≤ mu := by
  obtain ⟨f, hf, hp, hne, he⟩ := he
  obtain ⟨u, hu, hrec⟩ := exists_physical_reconstruction f hf hp
  subst f
  have hune : u ≠ 0 := by
    intro hz
    apply hne
    apply coeff_injective (1 / 2 : ℝ)
    funext l
    rw [coeff_traceOfSector]
    have hi : iotaTan 0 u = 0 := by
      funext i
      cases i <;> simp [iotaTan_inl, iotaTan_inr, coefT, hz]
    rw [hi]
    by_cases hm : ∃ i, idxToℤ i = l
    · obtain ⟨i, rfl⟩ := hm
      rw [sectorInsertCoeff_lattice]
      simp [coeff]
    · rw [sectorInsertCoeff_off _ l hm]
      simp [coeff]
  apply gam_le_coefficient_eigenvalue hu hune
  intro v hv
  have ht := he _ (memDomSigma_traceOfSector (iotaTan_mem_Domς 0 hv))
    (reconstructed_mem_positive v hv)
  change physicalForm s (physicalGraph v hv) (physicalGraph u hu) =
    inner ℂ (physicalTrace v hv) ((mu : ℂ) • physicalTrace u hu) at ht
  rw [physicalForm_eq_Bform, inner_smul_right, physicalTrace_inner] at ht
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : 0 < 2 * Real.pi))
  apply mul_left_cancel₀ hpi
  calc
    _ = (mu : ℂ) * ((2 * Real.pi : ℂ) * massPair v u) := ht
    _ = _ := by ring

/-- For positive parameters, gamma is the least physical eigenvalue. -/
theorem gam_isLeast_physicalEigenvalue {s : ℝ} (hs : 0 < s) :
    IsLeast {mu : ℝ | IsPhysicalEigenvalue s mu} (gam s) :=
  ⟨gam_isPhysicalEigenvalue hs, fun _ he => gam_le_physicalEigenvalue he⟩

end KsIndex.CircleQ
