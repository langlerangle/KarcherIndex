module

public import KsIndexLean.SphericalJoinedJet
public import KsIndexLean.SphericalChartQuotient

@[expose] public section


open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

lemma ae_stereoAreaMeasure_iff (P : ℂ → Prop) :
    (∀ᵐ z ∂stereoAreaMeasure, P z) ↔ ∀ᵐ z ∂(volume : Measure ℂ), P z := by
  rw [stereoAreaMeasure, ae_withDensity_iff continuous_stereoAreaDensity.measurable.ennreal_ofReal]
  have h (z : ℂ) : ENNReal.ofReal (stereoAreaDensity z) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (stereoAreaDensity_pos z))
  apply Filter.eventually_congr
  filter_upwards with z
  exact ⟨fun hz => hz (h z), fun hz _ => hz⟩

/-- Canonical area equality is exactly planar AE equality in either full chart. -/
lemma sphere_ae_eq_iff_north (F G : Sphere → ℂ) :
    F =ᵐ[(volume : Measure Ambient).toSphere] G ↔
      (fun z => F (sphereChart z)) =ᵐ[volume] (fun z => G (sphereChart z)) := by
  rw [← chartAreaMeasure_eq_toSphere, chartAreaMeasure]
  change (∀ᵐ p ∂Measure.map sphereChart stereoAreaMeasure, F p = G p) ↔ _
  rw [measurableEmbedding_sphereChart.ae_map_iff, ae_stereoAreaMeasure_iff]
  rfl

lemma sphere_ae_eq_iff_south (F G : Sphere → ℂ) :
    F =ᵐ[(volume : Measure Ambient).toSphere] G ↔
      (fun z => F (southChart z)) =ᵐ[volume] (fun z => G (southChart z)) := by
  rw [← chartAreaMeasure_eq_toSphere, ← map_southChart_stereoAreaMeasure]
  change (∀ᵐ p ∂Measure.map southChart stereoAreaMeasure, F p = G p) ↔ _
  rw [measurableEmbedding_southChart.ae_map_iff, ae_stereoAreaMeasure_iff]
  rfl

lemma sphereChartSetoid_iff_canonical {A : Set Circle₁} (hA : IsOpen A)
    (F G : SphereChartFunctions A hA) :
    (sphereChartSetoid A hA).r F G ↔
      F.val =ᵐ[(volume : Measure Ambient).toSphere] G.val := by
  change (_ ∧ _) ↔ _
  rw [← sphere_ae_eq_iff_north, ← sphere_ae_eq_iff_south, and_self]

lemma sphereChartClass_eq_iff_canonical {A : Set Circle₁} (hA : IsOpen A)
    (F G : SphereChartFunctions A hA) :
    (Quotient.mk (sphereChartSetoid A hA) F : SphereChartSpace A hA) =
      Quotient.mk (sphereChartSetoid A hA) G ↔
        F.val =ᵐ[(volume : Measure Ambient).toSphere] G.val := by
  rw [Quotient.eq, sphereChartSetoid_iff_canonical]

/-- The actual canonical L2 seminorm on the chart quotient; finiteness is separate. -/
def sphereChartL2 {A : Set Circle₁} (hA : IsOpen A) : SphereChartSpace A hA → ℝ≥0∞ :=
  Quotient.lift (fun F => eLpNorm F.val 2 (volume : Measure Ambient).toSphere)
    (fun F G h => eLpNorm_congr_ae ((sphereChartSetoid_iff_canonical hA F G).mp h))

lemma sphereChartL2_mk {A : Set Circle₁} (hA : IsOpen A) (F : SphereChartFunctions A hA) :
    sphereChartL2 hA (Quotient.mk (sphereChartSetoid A hA) F) =
      eLpNorm F.val 2 (volume : Measure Ambient).toSphere := rfl

lemma sphereChartL2_matchingPair {A : Set Circle₁} (hA : IsOpen A) (p : MatchingDiskPair A) :
    sphereChartL2 hA (matchingPairClass hA p) =
      eLpNorm (sphereJoinedValue p.val.1 p.val.2) 2 (volume : Measure Ambient).toSphere := rfl

lemma sphereChartL2_slit {A : Set Circle₁} (hA : IsOpen A)
    (F : SphereChartFunctions A hA) (k : ℕ) :
    sphereChartL2 hA (Quotient.mk (sphereChartSetoid A hA) F) =
      eLpNorm F.val 2 ((volume : Measure Ambient).toSphere.restrict (slitSphere k)) := by
  rw [canonicalArea_restrict_slitSphere]
  rfl

end KsIndex.Spherical
