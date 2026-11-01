module

public import KsIndexLean.DiskNegativeCoordinates
public import KsIndexLean.DiskFiniteNegativeIndex

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

variable (D : Submodule ℂ ComplexH1) [CompleteSpace D] (V : BoundedRealPotential)
  [FiniteDimensional ℂ (WeightedDiskAmbient D)]

lemma diskFiniteNegativeCount_le :
    (diskSpectralData D V).finiteStrictCount (V.C + 1) 0 ≤ Module.finrank ℂ (WeightedDiskAmbient D) := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin _)

def diskFiniteNegativeCoordinates : D →ₗ[ℂ]
    (Fin ((diskSpectralData D V).finiteStrictCount (V.C + 1) 0) → ℂ) where
  toFun u i := inner ℂ ((diskSpectralData D V).finiteEigenbasis
      ⟨i.val, i.isLt.trans_le (diskFiniteNegativeCount_le D V)⟩)
    (weightedDiskAmbientEmbedding D u)
  map_add' u v := by
    funext i
    simp only [map_add, inner_add_right, Pi.add_apply]
  map_smul' c u := by
    funext i
    simp only [map_smul, inner_smul_right, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

lemma diskFiniteNegativeCoordinates_kernel_nonnegative (u : D)
    (hu : diskFiniteNegativeCoordinates D V u = 0) : 0 ≤ (weakJacobi V u u).re := by
  classical
  let k := (diskSpectralData D V).finiteStrictCount (V.C + 1) 0
  let m := Module.finrank ℂ (WeightedDiskAmbient D)
  by_cases hk : k < m
  · let n : Fin m := ⟨k, hk⟩
    have hn : 0 ≤ (diskSpectralData D V).finiteReciprocalShift (V.C + 1) n := by
      by_contra hh
      have hl := (finite_lt_iff_lt_count
        ((diskSpectralData D V).finiteReciprocalShift (V.C + 1))
        ((diskSpectralData D V).finiteReciprocalShift_monotone (V.C + 1)) 0 n).mp (lt_of_not_ge hh)
      change k < k at hl
      omega
    have ht := diskJacobi_finite_spectral_tail D V n u (by
      intro i hi
      have he := congrFun hu ⟨i.val, hi⟩
      simpa only [diskFiniteNegativeCoordinates, LinearMap.coe_mk, AddHom.coe_mk,
        OrthonormalBasis.coe_toHilbertBasis, Pi.zero_apply] using he)
    exact (mul_nonneg hn (sq_nonneg _)).trans ht
  · have hmk : m ≤ k := Nat.le_of_not_gt hk
    have hz : weightedDiskAmbientEmbedding D u = 0 := by
      apply (diskSpectralData D V).finiteEigenbasis.repr.injective
      ext i
      rw [map_zero, OrthonormalBasis.repr_apply_apply]
      exact congrFun hu ⟨i.val, i.isLt.trans_le hmk⟩
    have hu0 : u = 0 := (weightedDiskAmbientEmbedding_spec D).1 (hz.trans (map_zero (weightedDiskAmbientEmbedding D)).symm)
    subst u
    have he : (weakJacobi V (0 : D) (0 : D)).re = 0 :=
      congrArg (fun f : D →L[ℂ] ℂ => (f 0).re) ((domainJacobiForm D V).toLinearMap.map_zero)
    exact he.ge

lemma diskFiniteNegativeCoordinates_dimension :
    KsIndex.NegativeDensity.negativeIndex (fun u : D => (weakJacobi V u u).re) =
      (Module.finrank ℂ (Fin ((diskSpectralData D V).finiteStrictCount (V.C + 1) 0) → ℂ) : ℕ∞) := by
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
    disk_negativeIndex_eq_finite_count D V


lemma diskJacobi_product_index_finite (A B : Submodule ℂ ComplexH1)
    [CompleteSpace A] [CompleteSpace B] (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedDiskAmbient A)]
    [FiniteDimensional ℂ (WeightedDiskAmbient B)] :
    KsIndex.NegativeDensity.negativeIndex
      (fun u : A × B => (weakJacobi V u.1 u.1).re + (weakJacobi V u.2 u.2).re) =
      KsIndex.NegativeDensity.negativeIndex (fun u : A => (weakJacobi V u u).re) +
      KsIndex.NegativeDensity.negativeIndex (fun u : B => (weakJacobi V u u).re) := by
  have hz (C : Submodule ℂ ComplexH1) : (weakJacobi V (0 : C) (0 : C)).re = 0 :=
    congrArg (fun f : C →L[ℂ] ℂ => (f 0).re) ((domainJacobiForm C V).toLinearMap.map_zero)
  exact negativeIndex_product_eq_of_coordinates
    (fun u : A => (weakJacobi V u u).re) (fun u : B => (weakJacobi V u u).re)
    (hz A) (hz B) (diskFiniteNegativeCoordinates A V) (diskFiniteNegativeCoordinates B V)
    (diskFiniteNegativeCoordinates_kernel_nonnegative A V)
    (diskFiniteNegativeCoordinates_kernel_nonnegative B V)
    (diskFiniteNegativeCoordinates_dimension A V) (diskFiniteNegativeCoordinates_dimension B V)

lemma diskJacobi_product_index_finite_infinite (A B : Submodule ℂ ComplexH1)
    [CompleteSpace A] [CompleteSpace B] (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedDiskAmbient A)]
    [Infinite (diskSpectralData B V).eigenbasisIndex] :
    KsIndex.NegativeDensity.negativeIndex
      (fun u : A × B => (weakJacobi V u.1 u.1).re + (weakJacobi V u.2 u.2).re) =
      KsIndex.NegativeDensity.negativeIndex (fun u : A => (weakJacobi V u u).re) +
      KsIndex.NegativeDensity.negativeIndex (fun u : B => (weakJacobi V u u).re) := by
  have hz (C : Submodule ℂ ComplexH1) : (weakJacobi V (0 : C) (0 : C)).re = 0 :=
    congrArg (fun f : C →L[ℂ] ℂ => (f 0).re) ((domainJacobiForm C V).toLinearMap.map_zero)
  exact negativeIndex_product_eq_of_coordinates
    (fun u : A => (weakJacobi V u u).re) (fun u : B => (weakJacobi V u u).re)
    (hz A) (hz B) (diskFiniteNegativeCoordinates A V) (diskNegativeCoordinates B V)
    (diskFiniteNegativeCoordinates_kernel_nonnegative A V)
    (diskNegativeCoordinates_kernel_nonnegative B V)
    (diskFiniteNegativeCoordinates_dimension A V) (diskNegativeCoordinates_dimension B V)

lemma diskJacobi_product_index_infinite_finite (A B : Submodule ℂ ComplexH1)
    [CompleteSpace A] [CompleteSpace B] (V : BoundedRealPotential)
    [Infinite (diskSpectralData A V).eigenbasisIndex]
    [FiniteDimensional ℂ (WeightedDiskAmbient B)] :
    KsIndex.NegativeDensity.negativeIndex
      (fun u : A × B => (weakJacobi V u.1 u.1).re + (weakJacobi V u.2 u.2).re) =
      KsIndex.NegativeDensity.negativeIndex (fun u : A => (weakJacobi V u u).re) +
      KsIndex.NegativeDensity.negativeIndex (fun u : B => (weakJacobi V u u).re) := by
  have hz (C : Submodule ℂ ComplexH1) : (weakJacobi V (0 : C) (0 : C)).re = 0 :=
    congrArg (fun f : C →L[ℂ] ℂ => (f 0).re) ((domainJacobiForm C V).toLinearMap.map_zero)
  exact negativeIndex_product_eq_of_coordinates
    (fun u : A => (weakJacobi V u u).re) (fun u : B => (weakJacobi V u u).re)
    (hz A) (hz B) (diskNegativeCoordinates A V) (diskFiniteNegativeCoordinates B V)
    (diskNegativeCoordinates_kernel_nonnegative A V)
    (diskFiniteNegativeCoordinates_kernel_nonnegative B V)
    (diskNegativeCoordinates_dimension A V) (diskFiniteNegativeCoordinates_dimension B V)

end KsIndex.Spectral
