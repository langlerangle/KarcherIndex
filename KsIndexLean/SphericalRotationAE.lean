module

public import KsIndexLean.SphericalRotation
public import KsIndexLean.SphericalCanonicalQuotient

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical

/-- Actual spherical rotation respects canonical-area representatives. -/
lemma rotateSphere_ae_pullback (θ : ℝ) {F G : Sphere → ℂ}
    (h : F =ᵐ[(volume : Measure Ambient).toSphere] G) :
    (fun p => F (rotateSphere θ p)) =ᵐ[(volume : Measure Ambient).toSphere]
      (fun p => G (rotateSphere θ p)) := by
  apply (sphere_ae_eq_iff_north _ _).mpr
  have hp := (KsIndex.Trace.measurePreserving_planeRotation θ).quasiMeasurePreserving.ae_eq_comp
    ((sphere_ae_eq_iff_north F G).mp h)
  filter_upwards [hp] with z hz
  simpa only [Function.comp_apply, rotateSphere_sphereChart] using hz

/-- Pullback in the geometric sphere is pullback by the same rotation in each chart. -/
lemma rotateSphere_chart_pullbacks (θ : ℝ) (F : Sphere → ℂ) :
    (fun z => F (rotateSphere θ (sphereChart z))) =
        (fun z => F (sphereChart (KsIndex.Trace.planeRotation θ z))) ∧
    (fun z => F (rotateSphere θ (southChart z))) =
        (fun z => F (southChart (KsIndex.Trace.planeRotation θ z))) := by
  simp only [rotateSphere_sphereChart, rotateSphere_southChart, and_self]

end KsIndex.Spherical
