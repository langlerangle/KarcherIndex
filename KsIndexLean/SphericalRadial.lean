module

public import KsIndexLean.RadialCharacter
public import KsIndexLean.BoundedH1Approximation
public import KsIndexLean.SphericalCutoffDomains

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- Nonlinear radial truncation preserves the transmission kernel. -/
def transmissionRadial (t : ℝ) (ht : 0 ≤ t) (A : Set Circle₁)
    (u : transmissionDomain A 1) : transmissionDomain A 1 :=
  ⟨(diskRadial t ht u.val.1, diskRadial t ht u.val.2),
    (mem_transmissionDomain A 1 _).mpr
      (diskRadial_arcTrace_phase t ht A 1 (norm_one : ‖(1 : ℂ)‖ = 1)
        ((mem_transmissionDomain A 1 u.val).mp u.property))⟩

/-- Radial truncation on the spherical carrier; this is not a linear map. -/
def sphereChartRadial (t : ℝ) (ht : 0 ≤ t) {A : Set Circle₁} (hA : IsOpen A)
    (q : SphereChartSpace A hA) : SphereChartSpace A hA :=
  (sphereTransmissionLinearIsometryEquiv A hA).symm
    (transmissionRadial t ht A (sphereTransmissionLinearIsometryEquiv A hA q))

lemma sphereChartRadial_coordinates (t : ℝ) (ht : 0 ≤ t) {A : Set Circle₁}
    (hA : IsOpen A) (q : SphereChartSpace A hA) :
    sphereDiskCoordinatesCLM hA (sphereChartRadial t ht hA q) =
      (diskRadial t ht (sphereDiskCoordinatesCLM hA q).1,
        diskRadial t ht (sphereDiskCoordinatesCLM hA q).2) := by
  change ((sphereTransmissionLinearIsometryEquiv A hA)
    ((sphereTransmissionLinearIsometryEquiv A hA).symm
      (transmissionRadial t ht A (sphereTransmissionLinearIsometryEquiv A hA q)))).val = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma sphereChartRadial_reflection (t : ℝ) (ht : 0 ≤ t) {A : Set Circle₁}
    (hA : IsOpen A) (q : SphereChartSpace A hA) :
    sphereChartRadial t ht hA (sphereChartReflectionEquiv hA q) =
      sphereChartReflectionEquiv hA (sphereChartRadial t ht hA q) := by
  apply sphereDiskCoordinates_injective hA
  rw [sphereChartRadial_coordinates, sphereChartReflection_coordinates,
    sphereChartReflection_coordinates, sphereChartRadial_coordinates]

lemma sphereChartRadial_phase (t : ℝ) (ht : 0 ≤ t) (k : ℕ) (c : ℂ) (hc : ‖c‖ = 1)
    {q : SphericalSlitNeumannSpace k} (hq : q ∈ sphericalPhaseDomain k c) :
    sphereChartRadial t ht (isOpen_boundaryArc k 1) q ∈ sphericalPhaseDomain k c := by
  change arcTrace (boundaryArc k 0) (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)
    (sphereChartRadial t ht (isOpen_boundaryArc k 1) q)).1 = c •
    arcTrace (boundaryArc k 0) (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)
      (sphereChartRadial t ht (isOpen_boundaryArc k 1) q)).2
  rw [sphereChartRadial_coordinates]
  exact diskRadial_arcTrace_phase t ht (boundaryArc k 0) c hc hq

lemma sphereChartRadial_character (t : ℝ) (ht : 0 ≤ t)
    {A : Set Circle₁} (hA : IsOpen A) (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A)
    (d : ℂ) (hd : ‖d‖ = 1) {q : SphereChartSpace A hA}
    (hq : q ∈ sphereChartCharacterDomain hA θ hθ d) :
    sphereChartRadial t ht hA q ∈ sphereChartCharacterDomain hA θ hθ d := by
  have h := (mem_sphereChartCharacterDomain_iff_pair hA θ hθ d q).mp hq
  rw [mem_sphereChartCharacterDomain_iff_pair, sphereChartRadial_coordinates]
  exact ⟨diskRadial_mem_weakCharacterDomain t ht θ d hd h.1,
    diskRadial_mem_weakCharacterDomain t ht θ d hd h.2⟩

lemma sphereChartRadial_tendsto {t : ℕ → ℝ} (ht : ∀ n, 0 ≤ t n)
    (ht0 : Tendsto t atTop (𝓝 0)) {A : Set Circle₁} (hA : IsOpen A)
    (q : SphereChartSpace A hA) :
    Tendsto (fun n => sphereChartRadial (t n) (ht n) hA q) atTop (𝓝 q) := by
  have hh : Tendsto (fun n => transmissionRadial (t n) (ht n) A
      (sphereTransmissionLinearIsometryEquiv A hA q)) atTop
      (𝓝 (sphereTransmissionLinearIsometryEquiv A hA q)) := by
    apply tendsto_subtype_rng.mpr
    exact (diskRadial_tendsto ht ht0 (sphereDiskCoordinatesCLM hA q).1).prodMk_nhds
      (diskRadial_tendsto ht ht0 (sphereDiskCoordinatesCLM hA q).2)
  have hc := (sphereTransmissionLinearIsometryEquiv A hA).symm.continuous
  have he := hc.continuousAt.tendsto.comp hh
  simp only [LinearIsometryEquiv.symm_apply_apply] at he
  exact he

end KsIndex.Spherical
