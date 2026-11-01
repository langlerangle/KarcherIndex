module

public import KsIndexLean.CylinderMetric
public import KsIndexLean.KarcherIntegerHeightArcs

@[expose] public section


/-! The round and cylindrical pullback metrics agree at every integer height. -/
noncomputable section
namespace KsIndex.KarcherData
open Cylindrical Spherical
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

/-- Every lift at normalized height nπ has a finite parameter on the unit circle. -/
theorem integerHeight_unit_parameter
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (n : ℤ)
    (hq : HeightLift.height q + Real.pi = (n : ℝ) * Real.pi) :
    ∃ w : PuncturedPlane k, HeightLift.projection q = finiteParameter w ∧ ‖w.val‖ = 1 := by
  have he := halfPeriod_height_intMul_pi_image_arc R.C R.hC n
  have hm : HeightLift.projection q ∈ finiteParameter ''
      {w : PuncturedPlane k | w.val ∈ Surface.arc k (n % 2).toNat} := by
    rw [← he]
    exact ⟨q, hq, rfl⟩
  obtain ⟨w, hw, hp⟩ := hm
  exact ⟨w, hp.symm, hw.1⟩

/-- The cylindrical and round densities agree at each integer-height point. -/
theorem integerHeight_metric_density
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (n : ℤ)
    (hq : HeightLift.height q + Real.pi = (n : ℝ) * Real.pi) :
    ∃ w : PuncturedPlane k, HeightLift.projection q = finiteParameter w ∧
      cylinderDensity w.val = stereoAreaDensity w.val := by
  obtain ⟨w, hw, hn⟩ := R.integerHeight_unit_parameter q n hq
  exact ⟨w, hw, cylinderDensity_eq_round_on_unit hn⟩

/-- Equality of the two rescaled actual immersion metrics, on every tangent
vector, at every integer normalized height (including negative heights). -/
theorem integerHeight_actual_metric
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (n : ℤ)
    (hq : HeightLift.height q + Real.pi = (n : ℝ) * Real.pi) :
    ∃ w : PuncturedPlane k, HeightLift.projection q = finiteParameter w ∧
      ∀ v : ℂ,
        (‖w.val‖ ^ 2 * Surface.rho k w.val ^ 2)⁻¹ *
          euclideanSq (fderiv ℝ (R.centeredChart q) w.val v) =
        (stereoAreaDensity w.val / Surface.rho k w.val ^ 2) *
          euclideanSq (fderiv ℝ (R.centeredChart q) w.val v) := by
  obtain ⟨w, hw, hn⟩ := R.integerHeight_unit_parameter q n hq
  refine ⟨w, hw, fun v => ?_⟩
  norm_num [hn, stereoAreaDensity_eq]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
