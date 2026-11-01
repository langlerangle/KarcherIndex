module

public import KsIndexLean.DiskNegativeIndex
public import KsIndexLean.NegativeProduct

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

variable (D : Submodule ℂ ComplexH1) [CompleteSpace D] (V : BoundedRealPotential)
  [Infinite (diskSpectralData D V).eigenbasisIndex]

/-- The actual negative spectral coefficients, retaining complex multiplicities. -/
def diskNegativeCoordinates : D →ₗ[ℂ] (Fin (diskNegativeCount D V) → ℂ) where
  toFun u i := inner ℂ ((diskSpectralData D V).infiniteEigenbasis i.val)
    (weightedDiskAmbientEmbedding D u)
  map_add' u v := by
    funext i
    simp only [map_add, inner_add_right, Pi.add_apply]
  map_smul' c u := by
    funext i
    simp only [map_smul, inner_smul_right, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

lemma diskNegativeCoordinates_kernel_nonnegative (u : D)
    (hu : diskNegativeCoordinates D V u = 0) : 0 ≤ (weakJacobi V u u).re := by
  have ht := diskJacobi_spectral_tail D V (diskNegativeCount D V) u (by
    intro i hi
    exact congrFun hu ⟨i, hi⟩)
  have hn : 0 ≤ (diskSpectralData D V).infiniteReciprocalShift (V.C + 1)
      (diskNegativeCount D V) := strictSpectralCount_spec _ _ 0
  exact (mul_nonneg hn (sq_nonneg _)).trans ht

lemma diskNegativeCoordinates_dimension :
    KsIndex.NegativeDensity.negativeIndex (fun u : D => (weakJacobi V u u).re) =
      (Module.finrank ℂ (Fin (diskNegativeCount D V) → ℂ) : ℕ∞) := by
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using disk_negativeIndex_eq_count D V


lemma diskJacobi_product_index_infinite (A B : Submodule ℂ ComplexH1)
    [CompleteSpace A] [CompleteSpace B] (V : BoundedRealPotential)
    [Infinite (diskSpectralData A V).eigenbasisIndex]
    [Infinite (diskSpectralData B V).eigenbasisIndex] :
    KsIndex.NegativeDensity.negativeIndex
      (fun u : A × B => (weakJacobi V u.1 u.1).re + (weakJacobi V u.2 u.2).re) =
      KsIndex.NegativeDensity.negativeIndex (fun u : A => (weakJacobi V u u).re) +
      KsIndex.NegativeDensity.negativeIndex (fun u : B => (weakJacobi V u u).re) := by
  have hz (C : Submodule ℂ ComplexH1) : (weakJacobi V (0 : C) (0 : C)).re = 0 :=
    congrArg (fun f : C →L[ℂ] ℂ => (f 0).re) ((domainJacobiForm C V).toLinearMap.map_zero)
  exact negativeIndex_product_eq_of_coordinates
    (fun u : A => (weakJacobi V u u).re) (fun u : B => (weakJacobi V u u).re)
    (hz A) (hz B) (diskNegativeCoordinates A V) (diskNegativeCoordinates B V)
    (diskNegativeCoordinates_kernel_nonnegative A V)
    (diskNegativeCoordinates_kernel_nonnegative B V)
    (diskNegativeCoordinates_dimension A V) (diskNegativeCoordinates_dimension B V)

end KsIndex.Spectral
