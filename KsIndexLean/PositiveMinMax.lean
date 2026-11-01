module

public import KsIndexLean.DiskJacobiMinMax

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

/-- Attainment excludes zero from an ordered min-max value of a positive
form, even when no uniform positive lower bound was supplied. -/
lemma positive_of_attained_minmax {E : Type*} [AddCommGroup E] [Module ℂ E]
    (Q M : E → ℝ) (hQ : ∀ u, u ≠ 0 → 0 < Q u) (d : ℕ) (hd : 0 < d)
    (lam : ℝ)
    (hm : ∀ L, lam ≤ L ↔ ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = d ∧ ∀ u : W, Q u ≤ L * M u) : 0 < lam := by
  by_contra h
  obtain ⟨W, hW, hdim, hb⟩ := (hm 0).mp (le_of_not_gt h)
  let := hW
  have hp : 0 < Module.finrank ℂ W := hdim.symm ▸ hd
  obtain ⟨u, hu⟩ := (Module.finrank_pos_iff_exists_ne_zero).mp hp
  have hu' : (u : E) ≠ 0 := fun he => hu (Subtype.ext he)
  have hpos := hQ u hu'
  have hbound := hb u
  simp only [zero_mul, not_le_of_gt hpos] at hbound

lemma diskJacobi_infinite_positive_of_positive (D : Submodule ℂ ComplexH1)
    [CompleteSpace D] (V : BoundedRealPotential)
    [Infinite (diskSpectralData D V).eigenbasisIndex]
    (hp : ∀ u : D, u ≠ 0 → 0 < (weakJacobi V u u).re) (n : ℕ) :
    0 < (diskSpectralData D V).infiniteReciprocalShift (V.C + 1) n :=
  positive_of_attained_minmax (fun u : D => (weakJacobi V u u).re)
    (fun u => ‖weightedDiskAmbientEmbedding D u‖ ^ 2) hp (n + 1) (by omega) _
    (diskJacobi_infinite_minmax D V n)

lemma diskJacobi_finite_positive_of_positive (D : Submodule ℂ ComplexH1)
    [CompleteSpace D] (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedDiskAmbient D)]
    (hp : ∀ u : D, u ≠ 0 → 0 < (weakJacobi V u u).re)
    (n : Fin (Module.finrank ℂ (WeightedDiskAmbient D))) :
    0 < (diskSpectralData D V).finiteReciprocalShift (V.C + 1) n :=
  positive_of_attained_minmax (fun u : D => (weakJacobi V u u).re)
    (fun u => ‖weightedDiskAmbientEmbedding D u‖ ^ 2) hp (n.val + 1) (by omega) _
    (diskJacobi_finite_minmax D V n)

end KsIndex.Spectral
