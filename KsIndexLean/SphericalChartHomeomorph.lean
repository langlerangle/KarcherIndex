module

public import KsIndexLean.SphericalAtlasBridge

@[expose] public section


open Set Metric

noncomputable section
namespace KsIndex.Spherical

lemma continuous_sphereChart : Continuous sphereChart :=
  contDiff_stereoPoint.continuous.subtype_mk _

lemma continuousOn_stereoCoord : ContinuousOn stereoCoord {p : Ambient | p 2 ≠ 1} := by
  apply ContinuousOn.div
  · change ContinuousOn (fun p : Ambient => Complex.mk (p 0) (p 1)) _
    have h : (fun p : Ambient => Complex.mk (p 0) (p 1)) =
        (fun p => (p 0 : ℂ) + (p 1 : ℂ) * Complex.I) := by
      funext p
      exact (Complex.re_add_im (Complex.mk (p 0) (p 1))).symm
    rw [h]
    fun_prop
  · change ContinuousOn (fun p : Ambient => ((1 - p 2 : ℝ) : ℂ)) _
    fun_prop
  · intro p hp
    change ((1 - p 2 : ℝ) : ℂ) ≠ 0
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hp.symm)

/-- The paper-normalized complex coordinate is a homeomorphism onto the punctured sphere. -/
def sphereChartHomeomorph : ℂ ≃ₜ {p : Sphere // p.val 2 ≠ 1} where
  toFun z := ⟨sphereChart z, stereoPoint_third_ne_one z⟩
  invFun p := stereoCoord p.val.val
  left_inv z := stereoCoord_stereoPoint z
  right_inv p := Subtype.ext (Subtype.ext (stereoPoint_stereoCoord p.val p.property))
  continuous_toFun := continuous_sphereChart.subtype_mk _
  continuous_invFun := continuousOn_stereoCoord.comp_continuous
    (continuous_subtype_val.comp continuous_subtype_val) (fun p => p.property)

end KsIndex.Spherical
