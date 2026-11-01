module

public import KsIndexLean.ConstrainedPunctureApproximation
public import KsIndexLean.SphericalReflectionDomains

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- Simultaneous cutoff on the closed transmission kernel. -/
def transmissionCutoff (k j : ℕ) (A : Set Circle₁) :
    transmissionDomain A 1 →L[ℂ] transmissionDomain A 1 :=
  ((diskCutoff k j).prodMap (diskCutoff k j)).restrict (by
    intro u hu
    apply (mem_transmissionDomain A 1 _).mpr
    exact diskCutoff_arcTrace_eq k j A 1 ((mem_transmissionDomain A 1 u).mp hu))

/-- The cutoff on the actual spherical weak carrier, through its established isometry. -/
def sphereChartCutoff (k j : ℕ) {A : Set Circle₁} (hA : IsOpen A) :
    SphereChartSpace A hA →L[ℂ] SphereChartSpace A hA :=
  let e := (sphereTransmissionLinearIsometryEquiv A hA).toContinuousLinearEquiv
  e.symm.toContinuousLinearMap.comp
    ((transmissionCutoff k j A).comp e.toContinuousLinearMap)

lemma sphereChartCutoff_coordinates (k j : ℕ) {A : Set Circle₁} (hA : IsOpen A)
    (q : SphereChartSpace A hA) :
    sphereDiskCoordinatesCLM hA (sphereChartCutoff k j hA q) =
      (diskCutoff k j (sphereDiskCoordinatesCLM hA q).1,
        diskCutoff k j (sphereDiskCoordinatesCLM hA q).2) := by
  change ((sphereTransmissionLinearIsometryEquiv A hA)
    ((sphereTransmissionLinearIsometryEquiv A hA).symm
      (transmissionCutoff k j A (sphereTransmissionLinearIsometryEquiv A hA q)))).val = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma sphereChartCutoff_reflection (k j : ℕ) {A : Set Circle₁} (hA : IsOpen A)
    (q : SphereChartSpace A hA) :
    sphereChartCutoff k j hA (sphereChartReflectionEquiv hA q) =
      sphereChartReflectionEquiv hA (sphereChartCutoff k j hA q) := by
  apply sphereDiskCoordinates_injective hA
  rw [sphereChartCutoff_coordinates, sphereChartReflection_coordinates,
    sphereChartReflection_coordinates, sphereChartCutoff_coordinates]

lemma sphereChartCutoff_phase (k j : ℕ) (c : ℂ) {q : SphericalSlitNeumannSpace k}
    (hq : q ∈ sphericalPhaseDomain k c) :
    sphereChartCutoff k j (isOpen_boundaryArc k 1) q ∈ sphericalPhaseDomain k c := by
  change arcTrace (boundaryArc k 0) (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)
    (sphereChartCutoff k j (isOpen_boundaryArc k 1) q)).1 = c •
    arcTrace (boundaryArc k 0) (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)
      (sphereChartCutoff k j (isOpen_boundaryArc k 1) q)).2
  rw [sphereChartCutoff_coordinates]
  exact diskCutoff_arcTrace_eq k j (boundaryArc k 0) c hq

lemma sphereChartCutoff_tendsto_of_bounded {k : ℕ} (hk : 1 ≤ k) {A : Set Circle₁}
    (hA : IsOpen A) (q : SphereChartSpace A hA) {M N : ℝ}
    (hu : ∀ᵐ z ∂volume.restrict disk, ‖valueCLM (sphereDiskCoordinatesCLM hA q).1 z‖ ≤ M)
    (hv : ∀ᵐ z ∂volume.restrict disk, ‖valueCLM (sphereDiskCoordinatesCLM hA q).2 z‖ ≤ N) :
    Tendsto (fun j => sphereChartCutoff k j hA q) atTop (𝓝 q) := by
  have ht : Tendsto (fun j => transmissionCutoff k j A
      (sphereTransmissionLinearIsometryEquiv A hA q)) atTop
      (𝓝 (sphereTransmissionLinearIsometryEquiv A hA q)) := by
    apply tendsto_subtype_rng.mpr
    exact slitCutoff_tendsto_of_bounded hk (sphereDiskCoordinatesCLM hA q) hu hv
  have hc := (sphereTransmissionLinearIsometryEquiv A hA).symm.continuous
  have he := hc.continuousAt.tendsto.comp ht
  simp only [LinearIsometryEquiv.symm_apply_apply] at he
  exact he

end KsIndex.Spherical
