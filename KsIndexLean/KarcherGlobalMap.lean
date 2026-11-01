module

public import KsIndexLean.KarcherParameterSphere

@[expose] public section


/-! Assemble the actual finite descended integral and its regular infinity
extension into a single map on the punctured parameter sphere. -/
noncomputable section
open scoped ContDiff
namespace KsIndex.KarcherData

/-- Finite coordinate of a non-north parameter point. -/
def finiteParameterCoordinate {k : ℕ} (p : ParameterSphere k) (hp : p.val.val 2 ≠ 1) :
    PuncturedPlane k :=
  ⟨Spherical.stereoCoord p.val.val, by
    intro hz
    exact p.property ⟨_, hz, Subtype.ext (Spherical.stereoPoint_stereoCoord p.val hp)⟩⟩

lemma finiteParameterCoordinate_finite {k : ℕ} (w : PuncturedPlane k)
    (h : (finiteParameter w).val.val 2 ≠ 1) :
    finiteParameterCoordinate (finiteParameter w) h = w := by
  apply Subtype.ext
  exact Spherical.stereoCoord_stereoPoint w.val

/-- Extend the based finite integral by a specified value at regular infinity.
The existence theorem below supplies that value from the integrated chart. -/
def extendedEWMap {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) (C : PeriodTarget)
    (p : ParameterSphere k) : PeriodTarget :=
  if h : p.val.val 2 = 1 then C else descendedIntegral hk b (finiteParameterCoordinate p h)

lemma extendedEWMap_finite {k : ℕ} (hk : 2 ≤ k) (b w : PuncturedPlane k)
    (C : PeriodTarget) : extendedEWMap hk b C (finiteParameter w) = descendedIntegral hk b w := by
  have hn : (finiteParameter w).val.val 2 ≠ 1 := Spherical.stereoPoint_third_ne_one w.val
  rw [extendedEWMap, dite_eq_right hn, finiteParameterCoordinate_finite]

lemma extendedEWMap_infinity {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k)
    (C : PeriodTarget) : extendedEWMap hk b C (infinityParameter k) = C := by
  apply dite_eq_left
  exact infinitySphereChart_zero_height

/-- The identified infinity primitive is the exact chart expression of the
single extended map, including at its center. -/
theorem extendedEWMap_infinityChart {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k)
    {r : ℝ} (hr : r ≤ 1) {X : ℂ → AmbientTriple} {C : PeriodTarget}
    (hzero : X 0 = 0)
    (hrep : ∀ v : infinityOverlap r,
      descendedIntegral hk b (infinityOverlapPoint hk hr v) = C + projectPeriod (X v.val))
    (v : Metric.ball (0 : ℂ) r) :
    extendedEWMap hk b C (infinityParameterChart hk hr v) = C + projectPeriod (X v.val) := by
  by_cases hv : v.val = 0
  · have he : infinityParameterChart hk hr v = infinityParameter k := by
      apply Subtype.ext
      change infinitySphereChart v.val = infinitySphereChart 0
      rw [hv]
    rw [he, extendedEWMap_infinity, hv, hzero, projectPeriod_zero, add_zero]
  · let q : infinityOverlap r := ⟨v.val, hv, by simpa only [Metric.mem_ball, dist_zero_right] using v.property⟩
    have he : infinityParameterChart hk hr v = finiteParameter (infinityOverlapPoint hk hr q) :=
      infinityParameterChart_overlap hk hr q
    rw [he, extendedEWMap_finite, hrep q]

/-- A single quotient-valued EW map on the punctured sphere has the actual
finite integral and a smooth nondegenerate infinity representative. The
parameter sphere is not asserted to be embedded as an ambient image. -/
theorem exists_extendedEWMap_geometry {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k) :
    ∃ r : ℝ, ∃ _hr0 : 0 < r, ∃ hr1 : r < 1,
    ∃ X : ℂ → AmbientTriple, ∃ C : PeriodTarget,
      (∀ w : PuncturedPlane k,
        extendedEWMap hk b C (finiteParameter w) = descendedIntegral hk b w) ∧
      (∀ v : Metric.ball (0 : ℂ) r,
        extendedEWMap hk b C (infinityParameterChart hk hr1.le v) = C + projectPeriod (X v.val)) ∧
      X 0 = 0 ∧ ContDiffOn ℝ ∞ X (Metric.ball (0 : ℂ) r) ∧
      HarmonicCoordinates X (Metric.ball (0 : ℂ) r) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) r, HasFDerivAt X (infinityRealDifferential k v) v) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) r, Function.Injective (infinityRealDifferential k v)) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) r, euclideanSq (chartUnitNormal X v) = 1 ∧
        chartMeanCurvature X v = 0 ∧
        conformalSecondFundamentalNorm X v (Surface.rho k v ^ 2) = Surface.absA k v) := by
  obtain ⟨r, hr0, hr1, X, C, hz, hs, hh, hd, hi, he, hg⟩ := exists_curvature_infinity_chart hk b
  exact ⟨r, hr0, hr1, X, C, fun w => extendedEWMap_finite hk b w C,
    extendedEWMap_infinityChart hk b hr1.le hz he, hz, hs, hh, hd, hi, hg⟩

/-- At every finite parameter point the same global map has a smooth harmonic
local representative with injective differential and zero mean curvature. -/
theorem extendedEWMap_finite_local_geometry {k : ℕ} (hk : 2 ≤ k)
    (b x : PuncturedPlane k) (C : PeriodTarget) :
    ∃ r : ℝ, 0 < r ∧ ∃ X : ℂ → AmbientTriple,
      X x.val = 0 ∧ ContDiffOn ℝ ∞ X (Metric.ball x.val r) ∧
      HarmonicCoordinates X (Metric.ball x.val r) ∧
      (∀ z ∈ Metric.ball x.val r, HasFDerivAt X (ewRealDifferential k z) z) ∧
      (∀ y : PuncturedPlane k, y.val ∈ Metric.ball x.val r →
        extendedEWMap hk b C (finiteParameter y) =
          extendedEWMap hk b C (finiteParameter x) + projectPeriod (X y.val)) ∧
      Function.Injective (ewRealDifferential k x.val) ∧
      (∀ z ∈ Metric.ball x.val r, chartMeanCurvature X z = 0) := by
  obtain ⟨r, hr, X, hz, hs, hh, hd, he, hH⟩ :=
    exists_zero_mean_curvature_local_representative hk b x
  refine ⟨r, hr, X, hz, hs, hh, hd, ?_, ewRealDifferential_injective hk x.property, hH⟩
  intro y hy
  rw [extendedEWMap_finite, extendedEWMap_finite]
  exact he y hy

end KsIndex.KarcherData
