module

public import KsIndexLean.SphericalWeakRotationValue
public import KsIndexLean.SphericalSlitLinear

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

lemma sphereDiskCoordinates_injective {A : Set Circle₁} (hA : IsOpen A) :
    Function.Injective (sphereDiskCoordinatesCLM hA) := by
  intro q r h
  apply (sphereTransmissionLinearIsometryEquiv A hA).injective
  exact Subtype.ext h

lemma sphereChartRotation_preserves_phase (k : ℕ) (c : ℂ) (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) (q : SphericalSlitPhaseSpace k c) :
    sphereChartRotationLI (isOpen_boundaryArc k 1) θ
      (circleRotate_boundaryArc_preimage k 1 θ hθ) q.val ∈ sphericalPhaseDomain k c := by
  change arcTrace (boundaryArc k 0) (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)
    (sphereChartRotationLI _ _ _ q.val)).1 = c • arcTrace (boundaryArc k 0)
      (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)
        (sphereChartRotationLI _ _ _ q.val)).2
  rw [sphereChartRotation_coordinates]
  exact arcTrace_rotation_phase _ (measurableSet_boundaryArc k 0) θ
    (circleRotate_boundaryArc_preimage k 0 θ hθ) c _ _ q.property

/-- Rotation restricted to the spherical slit phase domain. -/
def sphericalPhaseRotationLI (k : ℕ) (c : ℂ) (θ : ℝ)
    (hθ : Complex.exp (θ * Complex.I) ^ k = 1) :
    SphericalSlitPhaseSpace k c →ₗᵢ[ℂ] SphericalSlitPhaseSpace k c where
  toFun q := ⟨sphereChartRotationLI (isOpen_boundaryArc k 1) θ
    (circleRotate_boundaryArc_preimage k 1 θ hθ) q.val,
    sphereChartRotation_preserves_phase k c θ hθ q⟩
  map_add' q r := Subtype.ext (map_add _ q.val r.val)
  map_smul' a q := Subtype.ext (map_smul _ a q.val)
  norm_map' q := (sphereChartRotationLI (isOpen_boundaryArc k 1) θ
    (circleRotate_boundaryArc_preimage k 1 θ hθ)).norm_map q.val

/-- The closed character domain of the actual spherical rotation operator. -/
def sphereChartCharacterDomain {A : Set Circle₁} (hA : IsOpen A)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) (d : ℂ) :
    Submodule ℂ (SphereChartSpace A hA) :=
  LinearMap.ker ((sphereChartRotationLI hA θ hθ).toContinuousLinearMap -
    d • ContinuousLinearMap.id ℂ (SphereChartSpace A hA)).toLinearMap

lemma isClosed_sphereChartCharacterDomain {A : Set Circle₁} (hA : IsOpen A)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) (d : ℂ) :
    IsClosed (sphereChartCharacterDomain hA θ hθ d : Set (SphereChartSpace A hA)) :=
  ((sphereChartRotationLI hA θ hθ).toContinuousLinearMap -
    d • ContinuousLinearMap.id ℂ (SphereChartSpace A hA)).isClosed_ker

lemma mem_sphereChartCharacterDomain_iff_pair {A : Set Circle₁} (hA : IsOpen A)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) (d : ℂ) (q : SphereChartSpace A hA) :
    q ∈ sphereChartCharacterDomain hA θ hθ d ↔
      sphereDiskCoordinatesCLM hA q ∈ pairCharacterDomain θ d := by
  change sphereChartRotationLI hA θ hθ q - d • q = 0 ↔
    _ ∈ weakCharacterDomain θ d ∧ _ ∈ weakCharacterDomain θ d
  rw [sub_eq_zero]
  simp only [mem_weakCharacterDomain]
  constructor
  · intro h
    have he := congrArg (sphereDiskCoordinatesCLM hA) h
    rw [sphereChartRotation_coordinates, map_smul] at he
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  · rintro ⟨h1, h2⟩
    apply sphereDiskCoordinates_injective hA
    rw [sphereChartRotation_coordinates, map_smul]
    exact Prod.ext h1 h2

end KsIndex.Spherical
