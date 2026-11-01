module

public import KsIndexLean.KarcherMixedIndex
public import KsIndexLean.EncodingSpectralIndex
public import KsIndexLean.SectorInfinite
public import KsIndexLean.HemisphereWeakEigenspace

@[expose] public section


/-! Mixed half-period index as a negative-eigenvalue count.

The actual geometric compact-test index equals `diskNegativeCount` on
`mixedCharacterDomain k j true false`. The existing weak-domain spectral
identification supplies this count, with its infinite-dimensional spectral
instance discharged by `sector_eigenbasisIndex_infinite`.

The disk count represents the lower-hemisphere eigenvalue problem because
`classical_mixedHalfPeriod_hemisphere_eigenMultiplicity` identifies the
multiplicity at every level using the literal spherical-area L² pairing.
Preservation of the Jacobi form alone would not supply this mass identity.
The two results together give the spectral interpretation in the paper's
mixed-boundary conformal comparison.
-/
noncomputable section
open KsIndex.Spectral KsIndex.Trace KsIndex.WeakH1 KsIndex.SingleDisk
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- **Mixed half-period spectral count.** The compact mixed (Zaremba) core Morse index of the
geometric half period equals the negative-eigenvalue count `diskNegativeCount` of the weak form on
`mixedCharacterDomain k j true false` — the actual single-lower-hemisphere weak problem (see
`classical_mixedHalfPeriod_hemisphere_eigenMultiplicity` for the per-level identification of that
count with the literal hemisphere eigenvalue problem). -/
theorem halfPeriod_mixed_hemisphere_negativeCount (R : PaperHalfPeriodRealization k) (j : ℕ) :
    R.halfPeriodMixedIndex j =
      (@diskNegativeCount (mixedCharacterDomain k j true false) inferInstance (surfacePotential k)
        (sector_eigenbasisIndex_infinite k (by have := h.out; omega) j true false) : ℕ∞) := by
  have := sector_eigenbasisIndex_infinite k (show 0 < k by have := h.out; omega) j true false
  rw [R.halfPeriodMixedIndex_eq_seamNat]
  exact seamNat_eq_infinite_spectral_count h.out j true false

omit h in
/-- **Literal hemisphere eigenvalue identification.** At every level `L`, the actual
lower-hemisphere mixed eigenspace (defined by `hemisphereJacobi = L ·` the literal lower-hemisphere
L² mass) has the
same dimension as the disk eigenspace whose multiplicities `diskNegativeCount` sums. Thus the count
of `halfPeriod_mixed_hemisphere_negativeCount` is literally the displayed `Σ_{λ<0}` of the actual
single-hemisphere eigenvalue problem. -/
theorem classical_mixedHalfPeriod_hemisphere_eigenMultiplicity (j : ℕ) (L : ℝ) :
    Module.finrank ℂ (Spherical.hemisphereWeakEigenspace
        (mixedCharacterDomain k j true false) (surfacePotential k) L) =
      Module.finrank ℂ (diskWeakEigenspace
        (mixedCharacterDomain k j true false) (surfacePotential k) L) :=
  Spherical.hemisphereWeakEigenspace_finrank _ _ L

end KsIndex.KarcherData.PaperHalfPeriodRealization
