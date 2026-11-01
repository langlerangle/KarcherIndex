module

public import KsIndexLean.MixedCharacterUniqueness
public import KsIndexLean.DiskCommonEigenfunction

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical KsIndex.Trace KsIndex.FormIndex

lemma mixedDD_le_mixed (k j : ℕ) (b : Bool) :
    mixedCharacterDomain k j false false ≤ mixedCharacterDomain k j b (!b) := by
  intro u hu
  refine ⟨?_, hu.2⟩
  cases b
  · exact ⟨hu.1.1, Submodule.mem_top⟩
  · exact ⟨Submodule.mem_top, hu.1.2⟩

lemma mixed_dirichlet_eigenfunction_excluded {k : ℕ} (hk : 0 < k) (j : ℕ) (b : Bool)
    (lam : ℝ) (u : mixedCharacterDomain k j false false) (hu : u ≠ 0)
    (hQ : ∀ w : mixedCharacterDomain k j b (!b), weakJacobi (surfacePotential k) u w =
      (lam : ℂ) * inner ℂ (weightedDiskValueCLM u) (weightedDiskValueCLM w)) : False := by
  have hz := sphericalEigen_dirichlet_mixed_character_eq_zero hk j lam b u u.property
    (fun v hv => hQ ⟨v, hv⟩)
  exact hu (Subtype.ext hz)

/-- Strict mixed-to-Dirichlet ordering in the actual character domains. -/
lemma mixed_dirichlet_infinite_eigenvalue_lt {k : ℕ} (hk : 0 < k) (j : ℕ) (b : Bool)
    [Infinite (diskSpectralData (mixedCharacterDomain k j false false) (surfacePotential k)).eigenbasisIndex]
    [Infinite (diskSpectralData (mixedCharacterDomain k j b (!b)) (surfacePotential k)).eigenbasisIndex] (n : ℕ)
 :
    (diskSpectralData (mixedCharacterDomain k j b (!b)) (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1) n <
      (diskSpectralData (mixedCharacterDomain k j false false) (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1) n := by
  apply lt_of_le_of_ne (disk_infinite_eigenvalue_le (mixedCharacterDomain k j false false) (mixedCharacterDomain k j b (!b)) (surfacePotential k) (mixedDD_le_mixed k j b) n)
  intro heq
  obtain ⟨u, hu, hQ, _⟩ := disk_infinite_common_eigenfunction (mixedCharacterDomain k j false false) (mixedCharacterDomain k j b (!b)) (surfacePotential k) (mixedDD_le_mixed k j b) n heq.symm
  exact mixed_dirichlet_eigenfunction_excluded hk j b _ u hu hQ

/-- Strict mixed-to-Dirichlet ordering in the actual character domains. -/
lemma mixed_dirichlet_finite_to_infinite_eigenvalue_lt {k : ℕ} (hk : 0 < k) (j : ℕ) (b : Bool)
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedCharacterDomain k j false false))]
    [Infinite (diskSpectralData (mixedCharacterDomain k j b (!b)) (surfacePotential k)).eigenbasisIndex] (n : ℕ)
    (hD : n < Module.finrank ℂ (WeightedDiskAmbient (mixedCharacterDomain k j false false)))
 :
    (diskSpectralData (mixedCharacterDomain k j b (!b)) (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1) n <
      (diskSpectralData (mixedCharacterDomain k j false false) (surfacePotential k)).finiteReciprocalShift ((surfacePotential k).C + 1) ⟨n, hD⟩ := by
  apply lt_of_le_of_ne (disk_finite_to_infinite_eigenvalue_le (mixedCharacterDomain k j false false) (mixedCharacterDomain k j b (!b)) (surfacePotential k) (mixedDD_le_mixed k j b) n hD)
  intro heq
  obtain ⟨u, hu, hQ, _⟩ := disk_finite_to_infinite_common_eigenfunction (mixedCharacterDomain k j false false) (mixedCharacterDomain k j b (!b)) (surfacePotential k) (mixedDD_le_mixed k j b) n hD heq.symm
  exact mixed_dirichlet_eigenfunction_excluded hk j b _ u hu hQ

/-- Strict mixed-to-Dirichlet ordering in the actual character domains. -/
lemma mixed_dirichlet_infinite_to_finite_eigenvalue_lt {k : ℕ} (hk : 0 < k) (j : ℕ) (b : Bool)
    [Infinite (diskSpectralData (mixedCharacterDomain k j false false) (surfacePotential k)).eigenbasisIndex]
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedCharacterDomain k j b (!b)))] (n : ℕ)
    (hFdim : n < Module.finrank ℂ (WeightedDiskAmbient (mixedCharacterDomain k j b (!b))))
 :
    (diskSpectralData (mixedCharacterDomain k j b (!b)) (surfacePotential k)).finiteReciprocalShift ((surfacePotential k).C + 1) ⟨n, hFdim⟩ <
      (diskSpectralData (mixedCharacterDomain k j false false) (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1) n := by
  apply lt_of_le_of_ne (disk_infinite_to_finite_eigenvalue_le (mixedCharacterDomain k j false false) (mixedCharacterDomain k j b (!b)) (surfacePotential k) (mixedDD_le_mixed k j b) n hFdim)
  intro heq
  obtain ⟨u, hu, hQ, _⟩ := disk_infinite_to_finite_common_eigenfunction (mixedCharacterDomain k j false false) (mixedCharacterDomain k j b (!b)) (surfacePotential k) (mixedDD_le_mixed k j b) n hFdim heq.symm
  exact mixed_dirichlet_eigenfunction_excluded hk j b _ u hu hQ

/-- Strict mixed-to-Dirichlet ordering in the actual character domains. -/
lemma mixed_dirichlet_finite_eigenvalue_lt {k : ℕ} (hk : 0 < k) (j : ℕ) (b : Bool)
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedCharacterDomain k j false false))]
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedCharacterDomain k j b (!b)))] (n : ℕ)
    (hFdim : n < Module.finrank ℂ (WeightedDiskAmbient (mixedCharacterDomain k j b (!b))))
    (hD : n < Module.finrank ℂ (WeightedDiskAmbient (mixedCharacterDomain k j false false)))
 :
    (diskSpectralData (mixedCharacterDomain k j b (!b)) (surfacePotential k)).finiteReciprocalShift ((surfacePotential k).C + 1) ⟨n, hFdim⟩ <
      (diskSpectralData (mixedCharacterDomain k j false false) (surfacePotential k)).finiteReciprocalShift ((surfacePotential k).C + 1) ⟨n, hD⟩ := by
  apply lt_of_le_of_ne (disk_finite_eigenvalue_le (mixedCharacterDomain k j false false) (mixedCharacterDomain k j b (!b)) (surfacePotential k) (mixedDD_le_mixed k j b) n hD hFdim)
  intro heq
  obtain ⟨u, hu, hQ, _⟩ := disk_finite_common_eigenfunction (mixedCharacterDomain k j false false) (mixedCharacterDomain k j b (!b)) (surfacePotential k) (mixedDD_le_mixed k j b) n hFdim hD heq.symm
  exact mixed_dirichlet_eigenfunction_excluded hk j b _ u hu hQ

end KsIndex.Spectral
