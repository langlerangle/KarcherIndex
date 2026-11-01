module

public import KsIndexLean.ChainChartQuotient
public import KsIndexLean.SphericalCanonicalQuotient
public import KsIndexLean.SphericalHemisphereMeasure
public import Mathlib.Analysis.Normed.Module.TransferInstance

@[expose] public section


/-! Weak functions on a single actual lower hemisphere. No reflection or
second-hemisphere matching condition is part of this carrier. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- Weak H1 regularity in the stereographic coordinate of the lower hemisphere.
Values on its complement carry no conditions. -/
def HemisphereChartFunctions :=
  {F : Sphere → ℂ // ChartH1 disk (fun z => F (sphereChart z))}

def hemisphereChartSetoid : Setoid HemisphereChartFunctions where
  r F G := (fun z => F.val (sphereChart z)) =ᵐ[volume.restrict (disk : Set ℂ)]
    (fun z => G.val (sphereChart z))
  iseqv := ⟨fun _ => Filter.EventuallyEq.rfl,fun h => h.symm,fun h g => h.trans g⟩

/-- The quotient retains only the actual lower-hemisphere weak field. -/
def HemisphereChartSpace := Quotient hemisphereChartSetoid

/-- The chart quotient uses exactly equality almost everywhere for canonical
spherical area on the actual lower hemisphere. -/
lemma hemisphere_ae_eq_iff (F G : Sphere → ℂ) :
    F =ᵐ[(volume : Measure Ambient).toSphere.restrict {p : Sphere | p.val 2 < 0}] G ↔
      (fun z => F (sphereChart z)) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => G (sphereChart z)) := by
  rw [← sphereChart_disk_eq_lower,canonicalArea_restrict,
    Set.preimage_image_eq _ sphereChart_injective]
  change (∀ᵐ p ∂Measure.map sphereChart (stereoAreaMeasure.restrict (disk : Set ℂ)), F p = G p) ↔ _
  rw [measurableEmbedding_sphereChart.ae_map_iff]
  change (∀ᵐ z ∂stereoAreaMeasure.restrict (disk : Set ℂ), F (sphereChart z) = G (sphereChart z)) ↔ _
  rw [ae_restrict_iff' disk.isOpen.measurableSet,ae_stereoAreaMeasure_iff]
  exact (ae_restrict_iff' disk.isOpen.measurableSet).symm

lemma hemisphereChartSetoid_iff_canonical (F G : HemisphereChartFunctions) :
    hemisphereChartSetoid.r F G ↔
      F.val =ᵐ[(volume : Measure Ambient).toSphere.restrict {p : Sphere | p.val 2 < 0}] G.val :=
  (hemisphere_ae_eq_iff F.val G.val).symm

def hemisphereFunction (u : ComplexH1) : HemisphereChartFunctions :=
  ⟨sphereWeakValue u,by simpa only [sphereWeakValue_pullback] using carrier_chartH1_disk u⟩

def hemisphereClass (u : ComplexH1) : HemisphereChartSpace := Quotient.mk _ (hemisphereFunction u)

lemma hemisphereClass_injective : Function.Injective hemisphereClass := by
  intro u v he
  have hh := Quotient.exact he
  change (fun z => sphereWeakValue u (sphereChart z)) =ᵐ[volume.restrict (disk : Set ℂ)]
    (fun z => sphereWeakValue v (sphereChart z)) at hh
  simp only [sphereWeakValue_pullback] at hh
  exact valueCLM_injective (Lp.ext hh)

lemma hemisphereClass_surjective : Function.Surjective hemisphereClass := by
  intro q
  induction q using Quotient.inductionOn with
  | h F =>
    obtain ⟨u,hu,_⟩ := chartH1_disk_exists_unique F.property
    refine ⟨u,Quotient.sound ?_⟩
    change (fun z => sphereWeakValue u (sphereChart z)) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => F.val (sphereChart z))
    simpa only [sphereWeakValue_pullback] using hu

def hemisphereChartEquiv : ComplexH1 ≃ HemisphereChartSpace :=
  Equiv.ofBijective hemisphereClass ⟨hemisphereClass_injective,hemisphereClass_surjective⟩

instance hemisphereNormedAddCommGroup : NormedAddCommGroup HemisphereChartSpace :=
  hemisphereChartEquiv.symm.normedAddCommGroup
instance hemisphereModule : Module ℂ HemisphereChartSpace :=
  hemisphereChartEquiv.symm.addEquiv.module ℂ
instance hemisphereNormedSpace : NormedSpace ℂ HemisphereChartSpace :=
  hemisphereChartEquiv.symm.addEquiv.normedSpace ℂ

/-- Coordinates preserve the complete disk Sobolev norm; geometric integral
comparisons are established separately. -/
def hemisphereCoordinates : HemisphereChartSpace ≃ₗᵢ[ℂ] ComplexH1 where
  toLinearEquiv := hemisphereChartEquiv.symm.addEquiv.linearEquiv ℂ
  norm_map' _ := rfl

instance hemisphereCompleteSpace : CompleteSpace HemisphereChartSpace :=
  hemisphereCoordinates.toIsometryEquiv.completeSpace

@[simp] lemma hemisphereCoordinates_class (u : ComplexH1) :
    hemisphereCoordinates (hemisphereClass u) = u := hemisphereChartEquiv.symm_apply_apply u

/-- Recovering coordinates from a raw function gives its actual chart values
almost everywhere. -/
lemma hemisphereCoordinates_mk_value_ae (F : HemisphereChartFunctions) :
    valueCLM (hemisphereCoordinates (Quotient.mk hemisphereChartSetoid F))
      =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => F.val (sphereChart z)) := by
  have he : hemisphereClass (hemisphereCoordinates (Quotient.mk hemisphereChartSetoid F)) =
      Quotient.mk hemisphereChartSetoid F := hemisphereChartEquiv.apply_symm_apply _
  have hh := Quotient.exact he
  change (fun z => sphereWeakValue (hemisphereCoordinates (Quotient.mk hemisphereChartSetoid F))
    (sphereChart z)) =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => F.val (sphereChart z)) at hh
  simpa only [sphereWeakValue_pullback] using hh

/-- A spherical representative of a hemisphere weak field. -/
def hemisphereValue (u : HemisphereChartSpace) : Sphere → ℂ :=
  sphereWeakValue (hemisphereCoordinates u)

lemma hemisphereValue_mk_ae (F : HemisphereChartFunctions) :
    hemisphereValue (Quotient.mk hemisphereChartSetoid F)
      =ᵐ[(volume : Measure Ambient).toSphere.restrict {p : Sphere | p.val 2 < 0}] F.val := by
  apply (hemisphere_ae_eq_iff _ _).mpr
  simpa only [hemisphereValue,sphereWeakValue_pullback] using hemisphereCoordinates_mk_value_ae F

/-- The full canonical spherical Jacobi integral on just the lower hemisphere. -/
def hemisphereJacobi (V : BoundedRealPotential) (u v : HemisphereChartSpace) : ℂ :=
  ∫ p in {p : Sphere | p.val 2 < 0},
    tangentPair (sphereWeakGradient (hemisphereCoordinates u) p)
      (sphereWeakGradient (hemisphereCoordinates v) p) -
    (spherePotential V p : ℂ) * (starRingEnd ℂ) (sphereWeakValue (hemisphereCoordinates u) p) *
      sphereWeakValue (hemisphereCoordinates v) p ∂(volume : Measure Ambient).toSphere

/-- A single hemisphere has the disk form, without the doubled factor of a
signed two-hemisphere extension. -/
theorem hemisphereJacobi_eq (V : BoundedRealPotential) (u v : HemisphereChartSpace) :
    hemisphereJacobi V u v = weakJacobi V (hemisphereCoordinates u) (hemisphereCoordinates v) := by
  rw [weakJacobi_eq_sphere_integral,sphereChart_disk_eq_lower]
  rfl

end KsIndex.Spherical
