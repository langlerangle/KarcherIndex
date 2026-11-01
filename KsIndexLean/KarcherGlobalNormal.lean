module

public import KsIndexLean.KarcherRealConjugation

@[expose] public section


/-! The oriented Gauss field on the full EW parameter sphere, including infinity. -/
noncomputable section
namespace KsIndex.KarcherData

/-- The finite Gauss formula with its actual north-pole value at infinity. -/
def parameterNormal {k : ℕ} (p : ParameterSphere k) : AmbientTriple :=
  if h : p.val.val 2 = 1 then (0, 0, 1)
  else stereoNormal (gauss k (finiteParameterCoordinate p h).val)

lemma parameterNormal_finite {k : ℕ} (w : PuncturedPlane k) :
    parameterNormal (finiteParameter w) = stereoNormal (gauss k w.val) := by
  have hn : (finiteParameter w).val.val 2 ≠ 1 := Spherical.stereoPoint_third_ne_one w.val
  rw [parameterNormal, dite_eq_right hn, finiteParameterCoordinate_finite]

lemma parameterNormal_infinity (k : ℕ) :
    parameterNormal (infinityParameter k) = (0, 0, 1) := by
  exact dite_eq_left infinitySphereChart_zero_height

lemma parameterNormal_infinityChart {k : ℕ} (hk : 2 ≤ k) {r : ℝ} (hr : r ≤ 1)
    (v : Metric.ball (0 : ℂ) r) :
    parameterNormal (infinityParameterChart hk hr v) =
      normalHalfTurn (stereoNormal (gauss k v.val)) := by
  by_cases hv : v.val = 0
  · have he : infinityParameterChart hk hr v = infinityParameter k := by
      apply Subtype.ext
      change infinitySphereChart v.val = infinitySphereChart 0
      rw [hv]
    rw [he, parameterNormal_infinity, hv]
    simp [gauss, show k - 1 ≠ 0 by omega, stereoNormal, normalHalfTurn]
  · let q : infinityOverlap r := ⟨v.val, hv,
      by simpa only [Metric.mem_ball, dist_zero_right] using v.property⟩
    have he := infinityParameterChart_overlap hk hr q
    rw [he, parameterNormal_finite]
    change stereoNormal (gauss k v.val⁻¹) = _
    have hg : gauss k v.val ≠ 0 := pow_ne_zero _ hv
    rw [gauss_inv, stereoNormal_inv hg]

lemma continuous_parameterNormal {k : ℕ} (hk : 2 ≤ k) :
    Continuous (parameterNormal (k := k)) := by
  have hf : Continuous (parameterNormal (k := k) ∘ finiteParameter) := by
    have he : parameterNormal (k := k) ∘ finiteParameter =
        fun w : PuncturedPlane k => stereoNormal (gauss k w.val) :=
      funext parameterNormal_finite
    rw [he]
    exact continuous_stereoNormal.comp (continuous_subtype_val.pow (k - 1))
  have hi : Continuous (parameterNormal ∘ infinityParameterChart hk (le_refl (1 : ℝ))) := by
    have he : parameterNormal ∘ infinityParameterChart hk (le_refl (1 : ℝ)) =
        fun v : Metric.ball (0 : ℂ) 1 => normalHalfTurn (stereoNormal (gauss k v.val)) :=
      funext (parameterNormal_infinityChart hk (le_refl (1 : ℝ)))
    rw [he]
    have hn : Continuous normalHalfTurn := by unfold normalHalfTurn; fun_prop
    exact hn.comp (continuous_stereoNormal.comp (continuous_subtype_val.pow (k - 1)))
  rw [continuous_iff_continuousAt]
  intro p
  rcases parameterSphere_chart_cover hk (by norm_num : (0 : ℝ) < 1) (le_refl 1) p with
    ⟨w, rfl⟩ | ⟨v, rfl⟩
  · exact (isOpenEmbedding_finiteParameter k).continuousAt_iff.mp hf.continuousAt
  · exact (isOpenEmbedding_infinityParameterChart hk (le_refl 1)).continuousAt_iff.mp
      hi.continuousAt

/-- Agreement with the derivative-defined normal of every finite EW representative. -/
lemma parameterNormal_eq_finite_chartNormal {k : ℕ} (hk : 2 ≤ k)
    (w : PuncturedPlane k) {X : ℂ → AmbientTriple}
    (hd : HasFDerivAt X (ewRealDifferential k w.val) w.val) :
    parameterNormal (finiteParameter w) = chartUnitNormal X w.val := by
  rw [parameterNormal_finite, ew_chartUnitNormal_eq_stereoNormal hk w.property hd]

lemma parameterNormal_unit {k : ℕ} (hk : 2 ≤ k) (p : ParameterSphere k) :
    euclideanSq (parameterNormal p) = 1 := by
  rcases parameterSphere_cases p with rfl | ⟨w, rfl⟩
  · rw [parameterNormal_infinity]
    norm_num [euclideanSq]
  · have hd := (ewRealDifferential k w.val).hasFDerivAt (x := w.val)
    rw [parameterNormal_eq_finite_chartNormal hk w hd]
    exact (ew_chartUnitNormal_spec hk w.property hd).1

namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Pull back the global oriented Gauss field to the actual intrinsic EW carrier. -/
def normal (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) : AmbientTriple :=
  parameterNormal (HeightLift.projection q)

lemma continuous_normal (R : PaperHalfPeriodRealization k) : Continuous R.normal :=
  (continuous_parameterNormal h.out).comp HeightLift.continuous_projection

lemma normal_unit (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    euclideanSq (R.normal q) = 1 := parameterNormal_unit h.out _

lemma normal_finite (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) :
    R.normal q = stereoNormal (w.val ^ (k - 1)) := by
  unfold normal
  rw [hq, parameterNormal_finite]
  rfl

end PaperHalfPeriodRealization
end KsIndex.KarcherData
