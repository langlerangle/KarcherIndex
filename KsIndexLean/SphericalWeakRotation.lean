module

public import KsIndexLean.SphericalQuotientForms
public import KsIndexLean.ArcTraceRotation
public import KsIndexLean.DiskRotationForms

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- Componentwise rotation preserves the actual transmission kernel. -/
def transmissionRotationLI (A : Set Circle₁) (hA : MeasurableSet A) (c : ℂ)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) :
    transmissionDomain A c →ₗᵢ[ℂ] transmissionDomain A c where
  toFun u := ⟨(diskRotation θ u.val.1, diskRotation θ u.val.2),
    (mem_transmissionDomain A c _).mpr (arcTrace_rotation_phase A hA θ hθ c _ _
      ((mem_transmissionDomain A c _).mp u.property))⟩
  map_add' u v := by apply Subtype.ext; ext <;> simp
  map_smul' a u := by apply Subtype.ext; ext <;> simp
  norm_map' u := by
    change max ‖diskRotation θ u.val.1‖ ‖diskRotation θ u.val.2‖ = max ‖u.val.1‖ ‖u.val.2‖
    simp only [LinearIsometry.norm_map]

/-- Rotation on the spherical weak chart quotient, through the proved identification. -/
def sphereChartRotationLI {A : Set Circle₁} (hA : IsOpen A)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) :
    SphereChartSpace A hA →ₗᵢ[ℂ] SphereChartSpace A hA :=
  (sphereTransmissionLinearIsometryEquiv A hA).symm.toLinearIsometry.comp
    ((transmissionRotationLI A hA.measurableSet 1 θ hθ).comp
      (sphereTransmissionLinearIsometryEquiv A hA).toLinearIsometry)

lemma sphereChartRotation_coordinates {A : Set Circle₁} (hA : IsOpen A)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) (q : SphereChartSpace A hA) :
    sphereDiskCoordinatesCLM hA (sphereChartRotationLI hA θ hθ q) =
      (diskRotation θ (sphereDiskCoordinatesCLM hA q).1,
        diskRotation θ (sphereDiskCoordinatesCLM hA q).2) := by
  change ((sphereTransmissionLinearIsometryEquiv A hA)
    ((sphereTransmissionLinearIsometryEquiv A hA).symm
      (transmissionRotationLI A hA.measurableSet 1 θ hθ
        (sphereTransmissionLinearIsometryEquiv A hA q)))).val = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma sphereChartDirichlet_rotation {A : Set Circle₁} (hA : IsOpen A)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) (q r : SphereChartSpace A hA) :
    sphereChartDirichlet hA (sphereChartRotationLI hA θ hθ q)
      (sphereChartRotationLI hA θ hθ r) = sphereChartDirichlet hA q r := by
  simp only [sphereChartDirichlet, sphereChartRotation_coordinates, dirichlet_diskRotation]

lemma sphereChartJacobi_rotation {A : Set Circle₁} (hA : IsOpen A)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) (V : BoundedRealPotential)
    (hV : (fun z => V.V (planeRotation θ z)) =ᵐ[volume.restrict disk] V.V)
    (q r : SphereChartSpace A hA) :
    sphereChartJacobi hA V (sphereChartRotationLI hA θ hθ q)
      (sphereChartRotationLI hA θ hθ r) = sphereChartJacobi hA V q r := by
  simp only [sphereChartJacobi, sphereChartRotation_coordinates, weakJacobi_diskRotation θ V hV]

lemma sphereChartSurfaceJacobi_rotation {A : Set Circle₁} (hA : IsOpen A)
    (k : ℕ) (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) (q r : SphereChartSpace A hA) :
    sphereChartJacobi hA (surfacePotential k) (sphereChartRotationLI hA θ hθ q)
      (sphereChartRotationLI hA θ hθ r) = sphereChartJacobi hA (surfacePotential k) q r :=
  sphereChartJacobi_rotation hA θ hθ _ (Filter.Eventually.of_forall
    (surfacePotential_rotation k θ)) q r

end KsIndex.Spherical
