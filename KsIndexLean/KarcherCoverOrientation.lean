module

public import KsIndexLean.KarcherNormalComparison

@[expose] public section


/-! Fix the competing Gauss normal's orientation using a finite image above zero. -/
noncomputable section
namespace KsIndex.KarcherData

lemma parameterNormal_finite_ne_north {k : ℕ} (w : PuncturedPlane k) :
    parameterNormal (finiteParameter w) ≠ (0, 0, 1) := by
  intro he
  rw [parameterNormal_finite] at he
  have hh := congrArg (fun a : AmbientTriple => a.2.2) he
  exact Spherical.stereoPoint_third_ne_one (gauss k w.val) hh

namespace PaperHalfPeriodRealization
open scoped KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- If a competing spherical coordinate gives an actual normal field and is
finite at one lift of zero, its Gauss normal has the paper's orientation
everywhere. Finiteness is subsequently supplied by the half-period condition. -/
theorem cover_normal_orientation (R : PaperHalfPeriodRealization k)
    (f : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C → ParameterSphere k)
    (hf : Continuous f)
    (hu : ∀ q, euclideanDot
      (fderiv ℝ (R.centeredChart q) (R.chartCenter q) 1) (parameterNormal (f q)) = 0)
    (hv : ∀ q, euclideanDot
      (fderiv ℝ (R.centeredChart q) (R.chartCenter q) Complex.I) (parameterNormal (f q)) = 0)
    (q₀ : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hzero : HeightLift.projection q₀ = finiteParameter ⟨0, zero_not_puncture h.out⟩)
    (w : PuncturedPlane k) (hw : f q₀ = finiteParameter w) :
    (fun q => parameterNormal (f q)) = R.normal := by
  apply R.normal_unique_of_eq_at _ ((continuous_parameterNormal h.out).comp hf)
    (fun q => parameterNormal_unit h.out (f q)) hu hv q₀
  have hc : euclideanSq (chartUnitNormal (R.centeredChart q₀) (R.chartCenter q₀)) = 1 := by
    rw [← R.normal_eq_centeredChart q₀]
    exact R.normal_unit q₀
  have hs := chart_unit_normal_eq_or_neg (parameterNormal_unit h.out (f q₀)) hc (hu q₀) (hv q₀)
  rw [← R.normal_eq_centeredChart q₀] at hs
  rcases hs with he | he
  · exact he
  · have hbase : R.normal q₀ = (0, 0, -1) := by
      rw [R.normal_finite q₀ ⟨0, zero_not_puncture h.out⟩ hzero]
      have hk := h.out
      simp [stereoNormal, show k - 1 ≠ 0 by omega]
    rw [hbase, hw] at he
    have hnorth : parameterNormal (finiteParameter w) = (0, 0, 1) := by
      simpa only [Prod.neg_mk, neg_zero, neg_neg] using he
    exact (parameterNormal_finite_ne_north w hnorth).elim

/-- The finite half-period image condition fixes the orientation, with no
chosen anchor point or chosen orientation included as an extra hypothesis. -/
theorem cover_normal_orientation_of_halfPeriod (R : PaperHalfPeriodRealization k)
    (f : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C → ParameterSphere k)
    (hf : Continuous f)
    (hu : ∀ q, euclideanDot
      (fderiv ℝ (R.centeredChart q) (R.chartCenter q) 1) (parameterNormal (f q)) = 0)
    (hv : ∀ q, euclideanDot
      (fderiv ℝ (R.centeredChart q) (R.chartCenter q) Complex.I) (parameterNormal (f q)) = 0)
    (hfinite : ∀ q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C,
      ∃ w : PuncturedPlane k, f q.val = finiteParameter w) :
    (fun q => parameterNormal (f q)) = R.normal := by
  let z : PuncturedClosedDisk k := ⟨⟨0, zero_not_puncture h.out⟩, by norm_num⟩
  obtain ⟨q, hq⟩ := R.disk_bijective.surjective z
  have hp := R.projection_agrees q
  rw [hq] at hp
  obtain ⟨w, hw⟩ := hfinite q
  exact R.cover_normal_orientation f hf hu hv q.val hp.symm w hw

end PaperHalfPeriodRealization
end KsIndex.KarcherData
