module

public import KsIndexLean.SphericalSlitArea
public import KsIndexLean.SphericalPullbackH1

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1

/-- Hemispherewise tangent field associated with the joined disk values. -/
def sphereJoinedGradient (u v : ComplexH1) (p : Sphere) : Ambient × Ambient :=
  if p.val 2 ≤ 0 then sphereWeakGradient u p else southWeakGradient v p

def sphereJoinedPotential (V : BoundedRealPotential) (p : Sphere) : ℝ :=
  if p.val 2 ≤ 0 then spherePotential V p else spherePotential V (reflectSphere p)

def joinedJacobiDensity (V : BoundedRealPotential) (uN uS vN vS : ComplexH1)
    (p : Sphere) : ℂ :=
  tangentPair (sphereJoinedGradient uN uS p) (sphereJoinedGradient vN vS p) -
    (sphereJoinedPotential V p : ℂ) * (starRingEnd ℂ) (sphereJoinedValue uN uS p) *
      sphereJoinedValue vN vS p

lemma joinedJacobiDensity_ae (V : BoundedRealPotential) (uN uS vN vS : ComplexH1) :
    joinedJacobiDensity V uN uS vN vS =ᵐ[(volume : Measure Ambient).toSphere]
      twoChartJacobiDensity V uN uS vN vS := by
  classical
  have he : ∀ᵐ p ∂(volume : Measure Ambient).toSphere, p.val 2 ≠ 0 := by
    simpa only [ae_iff, not_not] using sphere_equator_null
  filter_upwards [he] with p hp
  by_cases h : p.val 2 < 0
  · have hm : p ∈ sphereChart '' (disk : Set ℂ) := by
      rw [sphereChart_disk_eq_lower]; exact h
    simp [joinedJacobiDensity, sphereJoinedGradient, sphereJoinedPotential,
      sphereJoinedValue, twoChartJacobiDensity, hm, h.le, sphereWeakValue]
  · have hpos : 0 < p.val 2 := lt_of_le_of_ne (le_of_not_gt h) hp.symm
    have hm : p ∉ sphereChart '' (disk : Set ℂ) := by
      rw [sphereChart_disk_eq_lower]; exact h
    simp [joinedJacobiDensity, sphereJoinedGradient, sphereJoinedPotential,
      sphereJoinedValue, twoChartJacobiDensity, hm, not_le.mpr hpos,
      southJacobiDensity, sphereWeakValue]

lemma integrable_joinedJacobiDensity (V : BoundedRealPotential)
    (uN uS vN vS : ComplexH1) :
    Integrable (joinedJacobiDensity V uN uS vN vS) (volume : Measure Ambient).toSphere :=
  (integrable_twoChartJacobiDensity V uN uS vN vS).congr
    (joinedJacobiDensity_ae V uN uS vN vS).symm

theorem sum_weakJacobi_eq_joined_integral (k : ℕ) (V : BoundedRealPotential)
    (uN uS vN vS : ComplexH1) :
    weakJacobi V uN vN + weakJacobi V uS vS =
      ∫ p in slitSphere k, joinedJacobiDensity V uN uS vN vS p
        ∂(volume : Measure Ambient).toSphere := by
  rw [canonicalArea_restrict_slitSphere, sum_weakJacobi_eq_sphere_integral]
  exact integral_congr_ae (joinedJacobiDensity_ae V uN uS vN vS).symm

lemma sphereJoinedGradient_north_disk (u v : ComplexH1) {z : ℂ} (hz : z ∈ disk) :
    sphereJoinedGradient u v (sphereChart z) = weakTangentGradient u z := by
  have h := (stereoPoint_lower_iff z).mpr (SurfaceForm.mem_disk_iff.mp hz)
  change (sphereChart z).val 2 < 0 at h
  rw [sphereJoinedGradient, ite_eq_left h.le, sphereWeakGradient_pullback]

lemma sphereJoinedGradient_north_represents (u v : ComplexH1) :
    ∀ᵐ z ∂volume.restrict (disk : Set ℂ), ∀ w : ℂ,
      (inner ℝ (sphereJoinedGradient u v (sphereChart z)).1
        (fderiv ℝ stereoPoint z w) : ℂ) +
      Complex.I * (inner ℝ (sphereJoinedGradient u v (sphereChart z)).2
        (fderiv ℝ stereoPoint z w) : ℂ) = weakDerivative u z w := by
  filter_upwards [ae_restrict_mem disk.isOpen.measurableSet,
    weakTangentGradient_represents u] with z hz h
  rw [sphereJoinedGradient_north_disk u v hz]
  exact h

lemma sphereJoinedGradient_south_disk (u v : ComplexH1) {z : ℂ} (hz : z ∈ disk) :
    sphereJoinedGradient u v (southChart z) =
      (reflectAmbient (weakTangentGradient v z).1,
        reflectAmbient (weakTangentGradient v z).2) := by
  have h := (stereoPoint_lower_iff z).mpr (SurfaceForm.mem_disk_iff.mp hz)
  have hp : ¬ (southChart z).val 2 ≤ 0 := by
    change ¬ -(stereoPoint z 2) ≤ 0
    linarith
  rw [sphereJoinedGradient, ite_eq_right hp, southWeakGradient_pullback]

/-- The reflected tangent field represents the south disk weak derivative
against reflected stereographic tangent vectors. -/
lemma sphereJoinedGradient_south_represents (u v : ComplexH1) :
    ∀ᵐ z ∂volume.restrict (disk : Set ℂ), ∀ w : ℂ,
      (inner ℝ (sphereJoinedGradient u v (southChart z)).1
        (reflectAmbient (fderiv ℝ stereoPoint z w)) : ℂ) +
      Complex.I * (inner ℝ (sphereJoinedGradient u v (southChart z)).2
        (reflectAmbient (fderiv ℝ stereoPoint z w)) : ℂ) = weakDerivative v z w := by
  filter_upwards [ae_restrict_mem disk.isOpen.measurableSet,
    weakTangentGradient_represents v] with z hz h
  intro w
  rw [sphereJoinedGradient_south_disk u v hz]
  simpa only [reflectAmbient_inner] using h w

end KsIndex.Spherical
