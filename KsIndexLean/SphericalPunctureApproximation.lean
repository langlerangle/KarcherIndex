module

public import KsIndexLean.SphericalRadialDomains

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.PunctureCutoff KsIndex.FaithfulInjection

/-- Arbitrary signed spherical H1 sectors admit bounded puncture-avoiding approximants
in the same sector. Rotation must preserve the puncture set. -/
theorem exists_signed_sphere_puncture_approx {k : ℕ} (hk : 1 ≤ k) (b1 b0 : Bool)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1)
    (d : ℂ) (hd : ‖d‖ = 1)
    (hroot : Complex.exp ((θ : ℂ) * Complex.I) ^ (2 * k) = 1)
    (q : SphericalSlitNeumannSpace k)
    (hq : q ∈ signedSphereSectorDomain k b1 b0 θ hθ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : SphericalSlitNeumannSpace k, ∃ M ρ : ℝ,
      v ∈ signedSphereSectorDomain k b1 b0 θ hθ d ∧ 0 < M ∧ 0 < ρ ∧ ‖v - q‖ < ε ∧
      (∀ᵐ z ∂volume.restrict disk,
        ‖valueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) v).1 z‖ ≤ M) ∧
      (∀ᵐ z ∂volume.restrict disk,
        ‖valueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) v).2 z‖ ≤ M) ∧
      (∀ᵐ z ∂volume.restrict disk,
        (∃ p ∈ Surface.punctures k, ‖z - p‖ ≤ ρ) →
          valueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) v).1 z = 0) ∧
      (∀ᵐ z ∂volume.restrict disk,
        (∃ p ∈ Surface.punctures k, ‖z - p‖ ≤ ρ) →
          valueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) v).2 z = 0) := by
  obtain ⟨w, M, hw, hM, hwq, hb1, hb2⟩ :=
    exists_signed_sphere_bounded_approx k b1 b0 θ hθ d hd q hq (half_pos hε)
  have hc := sphereChartCutoff_tendsto_of_bounded hk (isOpen_boundaryArc k 1) w hb1 hb2
  obtain ⟨j, hj⟩ := (Metric.tendsto_nhds.mp hc (ε / 2) (half_pos hε)).exists
  refine ⟨sphereChartCutoff k j (isOpen_boundaryArc k 1) w, M, (cutoffEps j) ^ 2,
    sphereChartCutoff_signedSector hk j b1 b0 θ hθ d hroot hw, hM,
    pow_pos (cutoffEps_pos j) 2, ?_, ?_, ?_, ?_, ?_⟩
  · have hj' : ‖sphereChartCutoff k j (isOpen_boundaryArc k 1) w - w‖ < ε / 2 := by
      simpa only [dist_eq_norm] using hj
    calc
      ‖sphereChartCutoff k j (isOpen_boundaryArc k 1) w - q‖ =
          ‖(sphereChartCutoff k j (isOpen_boundaryArc k 1) w - w) + (w - q)‖ := by
        congr 1
        abel
      _ ≤ ‖sphereChartCutoff k j (isOpen_boundaryArc k 1) w - w‖ + ‖w - q‖ :=
        norm_add_le _ _
      _ < ε := by linarith
  · rw [sphereChartCutoff_coordinates]
    exact diskCutoff_value_bound k j _ hb1
  · rw [sphereChartCutoff_coordinates]
    exact diskCutoff_value_bound k j _ hb2
  · rw [sphereChartCutoff_coordinates]
    exact diskCutoff_value_vanish_near hk j _
  · rw [sphereChartCutoff_coordinates]
    exact diskCutoff_value_vanish_near hk j _

end KsIndex.Spherical
