module

public import KsIndexLean.HemisphereH1Comparison
public import KsIndexLean.SphericalWeakPotential
public import KsIndexLean.HemisphereWeakDomains
public import KsIndexLean.SphericalBulkMap

@[expose] public section


/-! Polarized complex L² mass on the actual lower hemisphere.

The canonical spherical-area pairing equals the weighted disk L² inner product
after coordinate transport. This identity supplies the mass term in the weak
eigen-equation; it is separate from preservation of the Jacobi quadratic form.
The constructions apply to all of `HemisphereChartSpace`, and hence to its pure
and mixed character domains. Conjugation is in the first slot, as in `inner ℂ`.
-/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Spherical
open KsIndex.WeakH1

/-- The literal canonical lower-hemisphere L² mass pairing, conjugate-linear in the first slot. -/
def hemisphereMassPairing (u v : HemisphereChartSpace) : ℂ :=
  ∫ p in {p : Sphere | p.val 2 < 0},
    (starRingEnd ℂ) (hemisphereValue u p) * hemisphereValue v p
    ∂(volume : Measure Ambient).toSphere

/-- The mass pairing pulled back to the weighted disk area measure (polarized analogue of
`hemisphereMass_eq_chart`). -/
lemma hemisphereMassPairing_eq_chart (u v : HemisphereChartSpace) :
    hemisphereMassPairing u v = ∫ z in (disk : Set ℂ),
      (starRingEnd ℂ) (valueCLM (hemisphereCoordinates u) z) *
        valueCLM (hemisphereCoordinates v) z ∂stereoAreaMeasure := by
  unfold hemisphereMassPairing
  rw [← sphereChart_disk_eq_lower, canonicalArea_restrict,
    Set.preimage_image_eq _ sphereChart_injective,
    measurableEmbedding_sphereChart.integral_map]
  simp only [hemisphereValue, sphereWeakValue_pullback]

/-- The lower-hemisphere mass pairing equals the weighted disk L² inner product of the chart
coordinates. Neither `hemisphereCoordinates`
(a Sobolev isometry) nor `hemisphereDomainEquiv` is the L² isometry; the identity goes through the
measure/value change of variables. -/
lemma hemisphereMassPairing_eq_weightedValue_inner (u v : HemisphereChartSpace) :
    hemisphereMassPairing u v =
      inner ℂ (weightedDiskValueCLM (hemisphereCoordinates u))
        (weightedDiskValueCLM (hemisphereCoordinates v)) := by
  rw [hemisphereMassPairing_eq_chart, L2.inner_def]
  refine (integral_congr_ae ?_).symm
  filter_upwards [sphericalBulkMap_ae (valueCLM (hemisphereCoordinates u)),
    sphericalBulkMap_ae (valueCLM (hemisphereCoordinates v))] with z hz hz'
  change inner ℂ (sphericalBulkMap (valueCLM (hemisphereCoordinates u)) z)
      (sphericalBulkMap (valueCLM (hemisphereCoordinates v)) z)
    = (starRingEnd ℂ) (valueCLM (hemisphereCoordinates u) z) * valueCLM (hemisphereCoordinates v) z
  rw [hz, hz', RCLike.inner_apply]; ring

/-- The weighted ambient embedding inner product is the weighted value inner product. -/
lemma weightedDiskAmbientEmbedding_inner (D : Submodule ℂ ComplexH1) (w w' : D) :
    inner ℂ (weightedDiskAmbientEmbedding D w) (weightedDiskAmbientEmbedding D w') =
      inner ℂ (weightedDiskValueCLM w.val) (weightedDiskValueCLM w'.val) :=
  rfl

end KsIndex.Spherical
