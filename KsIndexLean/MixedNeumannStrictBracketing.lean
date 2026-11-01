module

public import KsIndexLean.SlitSeamGauges
public import KsIndexLean.NeumannStrictBracketing
public import KsIndexLean.NamedDomainSpectrum

@[expose] public section


noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma boundaryArc_one_nonempty (k : ℕ) : (boundaryArc k 1).Nonempty := by
  refine ⟨⟨1, mem_sphere_zero_iff_norm.mpr (by norm_num)⟩, ?_⟩
  rw [mem_boundaryArc]
  simp

lemma boundaryArc_zero_nonempty {k : ℕ} (hk : 0 < k) : (boundaryArc k 0).Nonempty := by
  refine ⟨circleParam (Real.pi / k), ?_⟩
  rw [mem_boundaryArc]
  have hp : ((circleParam (Real.pi / k) : Circle₁) : ℂ) ^ k = -1 := by
    rw [circleParam_coe, ← Complex.exp_nat_mul]
    have he : (k : ℂ) * ((Real.pi / k : ℝ) * Complex.I) = Real.pi * Complex.I := by
      push_cast
      have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
      field_simp
    rw [he, Complex.exp_pi_mul_I]
  rw [hp]
  norm_num

lemma mixedCharacterDomain_le_neumann (k j : ℕ) (b1 b0 : Bool) :
    mixedCharacterDomain k j b1 b0 ≤ mixedCharacterDomain k j true true := by
  simp only [mixedCharacterDomain, mixedTraceDomain_NN, top_inf_eq]
  exact inf_le_right

lemma mixedCharacterDomain_zero_arc {k : ℕ} (hk : 0 < k) (j : ℕ) (b1 b0 : Bool)
    (hb : b1 = false ∨ b0 = false) :
    ∃ A : Set Circle₁, IsOpen A ∧ A.Nonempty ∧ mixedCharacterDomain k j b1 b0 ≤ zeroTraceDomain A := by
  rcases hb with rfl | rfl
  · refine ⟨boundaryArc k 1, isOpen_boundaryArc k 1, boundaryArc_one_nonempty k, ?_⟩
    intro u hu
    exact hu.1.1
  · refine ⟨boundaryArc k 0, isOpen_boundaryArc k 0, boundaryArc_zero_nonempty hk, ?_⟩
    intro u hu
    exact hu.1.2

end KsIndex.Trace

namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical KsIndex.Trace KsIndex.FormIndex

/-- The paper's named mixed sector has strictly larger ordered eigenvalues
than its Neumann sector whenever at least one arc is Dirichlet. -/
lemma mixed_neumann_infinite_eigenvalue_lt {k : ℕ} (hk : 0 < k) (j : ℕ)
    (b1 b0 : Bool) (hb : b1 = false ∨ b0 = false)
    [Infinite (diskSpectralData (mixedCharacterDomain k j b1 b0) (surfacePotential k)).eigenbasisIndex]
    [Infinite (diskSpectralData (mixedCharacterDomain k j true true) (surfacePotential k)).eigenbasisIndex] (n : ℕ)
 :
    (diskSpectralData (mixedCharacterDomain k j true true) (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1) n <
      (diskSpectralData (mixedCharacterDomain k j b1 b0) (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1) n := by
  obtain ⟨A, hA, hne, hDA⟩ := mixedCharacterDomain_zero_arc hk j b1 b0 hb
  exact neumann_character_infinite_eigenvalue_lt hk j (mixedCharacterDomain k j b1 b0) (mixedCharacterDomain k j true true)
    (mixedCharacterDomain_le_neumann k j b1 b0)
    (by simp only [mixedCharacterDomain, mixedTraceDomain_NN, top_inf_eq]) A hA hne hDA n

/-- The paper's named mixed sector has strictly larger ordered eigenvalues
than its Neumann sector whenever at least one arc is Dirichlet. -/
lemma mixed_neumann_finite_to_infinite_eigenvalue_lt {k : ℕ} (hk : 0 < k) (j : ℕ)
    (b1 b0 : Bool) (hb : b1 = false ∨ b0 = false)
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedCharacterDomain k j b1 b0))]
    [Infinite (diskSpectralData (mixedCharacterDomain k j true true) (surfacePotential k)).eigenbasisIndex] (n : ℕ)
    (hD : n < Module.finrank ℂ (WeightedDiskAmbient (mixedCharacterDomain k j b1 b0)))
 :
    (diskSpectralData (mixedCharacterDomain k j true true) (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1) n <
      (diskSpectralData (mixedCharacterDomain k j b1 b0) (surfacePotential k)).finiteReciprocalShift ((surfacePotential k).C + 1) ⟨n, hD⟩ := by
  obtain ⟨A, hA, hne, hDA⟩ := mixedCharacterDomain_zero_arc hk j b1 b0 hb
  exact neumann_character_finite_to_infinite_eigenvalue_lt hk j (mixedCharacterDomain k j b1 b0) (mixedCharacterDomain k j true true)
    (mixedCharacterDomain_le_neumann k j b1 b0)
    (by simp only [mixedCharacterDomain, mixedTraceDomain_NN, top_inf_eq]) A hA hne hDA n hD

/-- The paper's named mixed sector has strictly larger ordered eigenvalues
than its Neumann sector whenever at least one arc is Dirichlet. -/
lemma mixed_neumann_infinite_to_finite_eigenvalue_lt {k : ℕ} (hk : 0 < k) (j : ℕ)
    (b1 b0 : Bool) (hb : b1 = false ∨ b0 = false)
    [Infinite (diskSpectralData (mixedCharacterDomain k j b1 b0) (surfacePotential k)).eigenbasisIndex]
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedCharacterDomain k j true true))] (n : ℕ)
    (hFdim : n < Module.finrank ℂ (WeightedDiskAmbient (mixedCharacterDomain k j true true)))
 :
    (diskSpectralData (mixedCharacterDomain k j true true) (surfacePotential k)).finiteReciprocalShift ((surfacePotential k).C + 1) ⟨n, hFdim⟩ <
      (diskSpectralData (mixedCharacterDomain k j b1 b0) (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1) n := by
  obtain ⟨A, hA, hne, hDA⟩ := mixedCharacterDomain_zero_arc hk j b1 b0 hb
  exact neumann_character_infinite_to_finite_eigenvalue_lt hk j (mixedCharacterDomain k j b1 b0) (mixedCharacterDomain k j true true)
    (mixedCharacterDomain_le_neumann k j b1 b0)
    (by simp only [mixedCharacterDomain, mixedTraceDomain_NN, top_inf_eq]) A hA hne hDA n hFdim

/-- The paper's named mixed sector has strictly larger ordered eigenvalues
than its Neumann sector whenever at least one arc is Dirichlet. -/
lemma mixed_neumann_finite_eigenvalue_lt {k : ℕ} (hk : 0 < k) (j : ℕ)
    (b1 b0 : Bool) (hb : b1 = false ∨ b0 = false)
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedCharacterDomain k j b1 b0))]
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedCharacterDomain k j true true))] (n : ℕ)
    (hFdim : n < Module.finrank ℂ (WeightedDiskAmbient (mixedCharacterDomain k j true true)))
    (hD : n < Module.finrank ℂ (WeightedDiskAmbient (mixedCharacterDomain k j b1 b0)))
 :
    (diskSpectralData (mixedCharacterDomain k j true true) (surfacePotential k)).finiteReciprocalShift ((surfacePotential k).C + 1) ⟨n, hFdim⟩ <
      (diskSpectralData (mixedCharacterDomain k j b1 b0) (surfacePotential k)).finiteReciprocalShift ((surfacePotential k).C + 1) ⟨n, hD⟩ := by
  obtain ⟨A, hA, hne, hDA⟩ := mixedCharacterDomain_zero_arc hk j b1 b0 hb
  exact neumann_character_finite_eigenvalue_lt hk j (mixedCharacterDomain k j b1 b0) (mixedCharacterDomain k j true true)
    (mixedCharacterDomain_le_neumann k j b1 b0)
    (by simp only [mixedCharacterDomain, mixedTraceDomain_NN, top_inf_eq]) A hA hne hDA n hFdim hD

end KsIndex.Spectral
