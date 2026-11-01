module

public import KsIndexLean.CharacterEigenTestExtension
public import KsIndexLean.DiskCommonEigenfunction
public import KsIndexLean.DiskBracketing

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical KsIndex.Trace KsIndex.FormIndex

lemma neumann_character_eigenfunction_excluded {k : ℕ} (hk : 0 < k) (j : ℕ)
    (D F : Submodule ℂ ComplexH1) (h : D ≤ F)
    (hF : F = weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (A : Set Circle₁) (hA : IsOpen A) (hne : A.Nonempty) (hDA : D ≤ zeroTraceDomain A)
    (lam : ℝ) (u : D) (hu : u ≠ 0)
    (hQ : ∀ w : F, weakJacobi (surfacePotential k) (Submodule.inclusion h u) w =
      (lam : ℂ) * inner ℂ (weightedDiskAmbientEmbedding F (Submodule.inclusion h u))
        (weightedDiskAmbientEmbedding F w)) : False := by
  have huc : (u : ComplexH1) ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) := by
    rw [← hF]
    exact h u.property
  have hz := sphericalEigen_neumann_character_openArc_eq_zero hk j lam u huc
    (fun v hv => hQ ⟨v, by rw [hF]; exact hv⟩) A hA hne (hDA u.property)
  exact hu (Subtype.ext hz)

/-- Strict comparison with a Neumann character sector when the smaller domain
has zero trace on a nonempty open arc. -/
lemma neumann_character_infinite_eigenvalue_lt {k : ℕ} (hk : 0 < k) (j : ℕ)
    (D F : Submodule ℂ ComplexH1) [CompleteSpace D] [CompleteSpace F]
    (h : D ≤ F) (hF : F = weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (A : Set Circle₁) (hA : IsOpen A) (hne : A.Nonempty) (hDA : D ≤ zeroTraceDomain A)
    [Infinite (diskSpectralData D (surfacePotential k)).eigenbasisIndex]
    [Infinite (diskSpectralData F (surfacePotential k)).eigenbasisIndex] (n : ℕ)
 :
    (diskSpectralData F (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1) n <
      (diskSpectralData D (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1) n := by
  apply lt_of_le_of_ne (disk_infinite_eigenvalue_le D F (surfacePotential k) h n)
  intro heq
  obtain ⟨u, hu, hQ, _⟩ := disk_infinite_common_eigenfunction D F (surfacePotential k) h n heq.symm
  exact neumann_character_eigenfunction_excluded hk j D F h hF A hA hne hDA _ u hu hQ

/-- Strict comparison with a Neumann character sector when the smaller domain
has zero trace on a nonempty open arc. -/
lemma neumann_character_finite_to_infinite_eigenvalue_lt {k : ℕ} (hk : 0 < k) (j : ℕ)
    (D F : Submodule ℂ ComplexH1) [CompleteSpace D] [CompleteSpace F]
    (h : D ≤ F) (hF : F = weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (A : Set Circle₁) (hA : IsOpen A) (hne : A.Nonempty) (hDA : D ≤ zeroTraceDomain A)
    [FiniteDimensional ℂ (WeightedDiskAmbient D)]
    [Infinite (diskSpectralData F (surfacePotential k)).eigenbasisIndex] (n : ℕ)
    (hD : n < Module.finrank ℂ (WeightedDiskAmbient D))
 :
    (diskSpectralData F (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1) n <
      (diskSpectralData D (surfacePotential k)).finiteReciprocalShift ((surfacePotential k).C + 1) ⟨n, hD⟩ := by
  apply lt_of_le_of_ne (disk_finite_to_infinite_eigenvalue_le D F (surfacePotential k) h n hD)
  intro heq
  obtain ⟨u, hu, hQ, _⟩ := disk_finite_to_infinite_common_eigenfunction D F (surfacePotential k) h n hD heq.symm
  exact neumann_character_eigenfunction_excluded hk j D F h hF A hA hne hDA _ u hu hQ

/-- Strict comparison with a Neumann character sector when the smaller domain
has zero trace on a nonempty open arc. -/
lemma neumann_character_infinite_to_finite_eigenvalue_lt {k : ℕ} (hk : 0 < k) (j : ℕ)
    (D F : Submodule ℂ ComplexH1) [CompleteSpace D] [CompleteSpace F]
    (h : D ≤ F) (hF : F = weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (A : Set Circle₁) (hA : IsOpen A) (hne : A.Nonempty) (hDA : D ≤ zeroTraceDomain A)
    [Infinite (diskSpectralData D (surfacePotential k)).eigenbasisIndex]
    [FiniteDimensional ℂ (WeightedDiskAmbient F)] (n : ℕ)
    (hFdim : n < Module.finrank ℂ (WeightedDiskAmbient F))
 :
    (diskSpectralData F (surfacePotential k)).finiteReciprocalShift ((surfacePotential k).C + 1) ⟨n, hFdim⟩ <
      (diskSpectralData D (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1) n := by
  apply lt_of_le_of_ne (disk_infinite_to_finite_eigenvalue_le D F (surfacePotential k) h n hFdim)
  intro heq
  obtain ⟨u, hu, hQ, _⟩ := disk_infinite_to_finite_common_eigenfunction D F (surfacePotential k) h n hFdim heq.symm
  exact neumann_character_eigenfunction_excluded hk j D F h hF A hA hne hDA _ u hu hQ

/-- Strict comparison with a Neumann character sector when the smaller domain
has zero trace on a nonempty open arc. -/
lemma neumann_character_finite_eigenvalue_lt {k : ℕ} (hk : 0 < k) (j : ℕ)
    (D F : Submodule ℂ ComplexH1) [CompleteSpace D] [CompleteSpace F]
    (h : D ≤ F) (hF : F = weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (A : Set Circle₁) (hA : IsOpen A) (hne : A.Nonempty) (hDA : D ≤ zeroTraceDomain A)
    [FiniteDimensional ℂ (WeightedDiskAmbient D)]
    [FiniteDimensional ℂ (WeightedDiskAmbient F)] (n : ℕ)
    (hFdim : n < Module.finrank ℂ (WeightedDiskAmbient F))
    (hD : n < Module.finrank ℂ (WeightedDiskAmbient D))
 :
    (diskSpectralData F (surfacePotential k)).finiteReciprocalShift ((surfacePotential k).C + 1) ⟨n, hFdim⟩ <
      (diskSpectralData D (surfacePotential k)).finiteReciprocalShift ((surfacePotential k).C + 1) ⟨n, hD⟩ := by
  apply lt_of_le_of_ne (disk_finite_eigenvalue_le D F (surfacePotential k) h n hD hFdim)
  intro heq
  obtain ⟨u, hu, hQ, _⟩ := disk_finite_common_eigenfunction D F (surfacePotential k) h n hFdim hD heq.symm
  exact neumann_character_eigenfunction_excluded hk j D F h hF A hA hne hDA _ u hu hQ

end KsIndex.Spectral
