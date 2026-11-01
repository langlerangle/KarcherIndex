module

public import KsIndexLean.CountInequalityWiring
public import KsIndexLean.InfiniteSolutionOrdering
public import KsIndexLean.SphericalBulkMap
public import KsIndexLean.SectorInfiniteFamily

@[expose] public section


/-!
# Infinite eigenbasis index sets for mixed character sectors

For `k > 0`, every mixed character sector has an infinite eigenbasis index
set for its disk spectral data. Here `eigenbasisIndex` labels the spectral
basis; infinitude of this set is not a claim that the negative form index
is infinite.

The first lemma reduces the result to infinite dimensionality of the sector.
The injective map `weightedDiskAmbientEmbedding` transfers that property to
the weighted ambient space, and `eigenbasisIndex_infinite` then applies.
The final theorem supplies the infinite-dimensionality hypothesis using
`mixedCharacterDomain_not_finiteDimensional`.
-/

noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical KsIndex.Trace KsIndex.FormIndex

/-- An infinite-dimensional sector has an infinite eigenbasis index set,
via its injective weighted ambient embedding. -/
lemma sector_eigenbasisIndex_infinite_of_not_finiteDimensional
    (k j : ℕ) (b₁ b₀ : Bool)
    (hfd : ¬ FiniteDimensional ℂ (mixedCharacterDomain k j b₁ b₀)) :
    Infinite (diskSpectralData (mixedCharacterDomain k j b₁ b₀)
      (surfacePotential k)).eigenbasisIndex := by
  apply (diskSpectralData (mixedCharacterDomain k j b₁ b₀)
    (surfacePotential k)).eigenbasisIndex_infinite
  intro hamb
  apply hfd
  have := hamb
  exact FiniteDimensional.of_injective
    (weightedDiskAmbientEmbedding (mixedCharacterDomain k j b₁ b₀)).toLinearMap
    (weightedDiskAmbientEmbedding_spec (mixedCharacterDomain k j b₁ b₀)).1

/-- For `k > 0`, the disk spectral data of every mixed character sector have
an infinite eigenbasis index set. The sector's infinite dimensionality is
supplied by `mixedCharacterDomain_not_finiteDimensional`. -/
theorem sector_eigenbasisIndex_infinite (k : ℕ) (hk : 0 < k) (j : ℕ) (b₁ b₀ : Bool) :
    Infinite (diskSpectralData (mixedCharacterDomain k j b₁ b₀)
      (surfacePotential k)).eigenbasisIndex :=
  sector_eigenbasisIndex_infinite_of_not_finiteDimensional k j b₁ b₀
    (KsIndex.Trace.mixedCharacterDomain_not_finiteDimensional k j hk b₁ b₀)

end KsIndex.Spectral
