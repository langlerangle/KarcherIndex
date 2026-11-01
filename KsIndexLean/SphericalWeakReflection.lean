module

public import KsIndexLean.SphericalPhaseRotation

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- Swapping the disk components preserves ordinary transmission. -/
def transmissionReflectionEquiv (A : Set Circle₁) :
    transmissionDomain A 1 ≃ₗᵢ[ℂ] transmissionDomain A 1 where
  toFun u := ⟨(u.val.2, u.val.1), by
    rw [mem_transmissionDomain]
    have h := (mem_transmissionDomain A 1 u.val).mp u.property
    simpa only [one_smul] using h.symm⟩
  invFun u := ⟨(u.val.2, u.val.1), by
    rw [mem_transmissionDomain]
    have h := (mem_transmissionDomain A 1 u.val).mp u.property
    simpa only [one_smul] using h.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' u := max_comm ‖u.val.2‖ ‖u.val.1‖

/-- Equatorial reflection on the actual spherical weak chart quotient. -/
def sphereChartReflectionEquiv {A : Set Circle₁} (hA : IsOpen A) :
    SphereChartSpace A hA ≃ₗᵢ[ℂ] SphereChartSpace A hA :=
  ((sphereTransmissionLinearIsometryEquiv A hA).trans (transmissionReflectionEquiv A)).trans
    (sphereTransmissionLinearIsometryEquiv A hA).symm

lemma sphereChartReflection_coordinates {A : Set Circle₁} (hA : IsOpen A)
    (q : SphereChartSpace A hA) :
    sphereDiskCoordinatesCLM hA (sphereChartReflectionEquiv hA q) =
      ((sphereDiskCoordinatesCLM hA q).2, (sphereDiskCoordinatesCLM hA q).1) := by
  change ((sphereTransmissionLinearIsometryEquiv A hA)
    ((sphereTransmissionLinearIsometryEquiv A hA).symm
      (transmissionReflectionEquiv A (sphereTransmissionLinearIsometryEquiv A hA q)))).val = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma sphereChartReflection_involutive {A : Set Circle₁} (hA : IsOpen A) :
    Function.Involutive (sphereChartReflectionEquiv hA) := by
  intro q
  apply sphereDiskCoordinates_injective hA
  rw [sphereChartReflection_coordinates, sphereChartReflection_coordinates]

lemma sphereJoinedValue_reflection (u v : ComplexH1) :
    sphereJoinedValue v u =ᵐ[(volume : Measure Ambient).toSphere]
      (fun p => sphereJoinedValue u v (reflectSphere p)) := by
  apply (sphere_ae_eq_iff_north _ _).mpr
  filter_upwards [(sphereJoinedValue_south_ae u v).symm] with z hz
  simpa only [sphereJoinedValue_north, southChart] using hz

lemma sphereChartReflection_value_ae {A : Set Circle₁} (hA : IsOpen A)
    (q : SphereChartSpace A hA) :
    sphereChartValue hA (sphereChartReflectionEquiv hA q) =ᵐ[
      (volume : Measure Ambient).toSphere] (fun p => sphereChartValue hA q (reflectSphere p)) := by
  change sphereJoinedValue (sphereDiskCoordinatesCLM hA
    (sphereChartReflectionEquiv hA q)).1 (sphereDiskCoordinatesCLM hA
    (sphereChartReflectionEquiv hA q)).2 =ᵐ[_] _
  rw [sphereChartReflection_coordinates]
  exact sphereJoinedValue_reflection _ _

lemma sphereChartDirichlet_reflection {A : Set Circle₁} (hA : IsOpen A)
    (q r : SphereChartSpace A hA) :
    sphereChartDirichlet hA (sphereChartReflectionEquiv hA q) (sphereChartReflectionEquiv hA r) =
      sphereChartDirichlet hA q r := by
  simp only [sphereChartDirichlet, sphereChartReflection_coordinates]
  exact add_comm _ _

lemma sphereChartJacobi_reflection {A : Set Circle₁} (hA : IsOpen A) (V : BoundedRealPotential)
    (q r : SphereChartSpace A hA) :
    sphereChartJacobi hA V (sphereChartReflectionEquiv hA q) (sphereChartReflectionEquiv hA r) =
      sphereChartJacobi hA V q r := by
  simp only [sphereChartJacobi, sphereChartReflection_coordinates]
  exact add_comm _ _

lemma sphereChartReflection_rotation_commute {A : Set Circle₁} (hA : IsOpen A)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) (q : SphereChartSpace A hA) :
    sphereChartReflectionEquiv hA (sphereChartRotationLI hA θ hθ q) =
      sphereChartRotationLI hA θ hθ (sphereChartReflectionEquiv hA q) := by
  apply sphereDiskCoordinates_injective hA
  simp only [sphereChartReflection_coordinates, sphereChartRotation_coordinates]

end KsIndex.Spherical
