module

public import KsIndexLean.SphericalRadial

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.SingleDisk

lemma sphereChartRadial_reflectionDomain (t : ℝ) (ht : 0 ≤ t) (k : ℕ) (b : Bool)
    {q : SphericalSlitNeumannSpace k} (hq : q ∈ sphereReflectionDomain k b) :
    sphereChartRadial t ht (isOpen_boundaryArc k 1) q ∈ sphereReflectionDomain k b := by
  rw [mem_sphereReflectionDomain_iff, sphereChartRadial_coordinates]
  rw [(mem_sphereReflectionDomain_iff k b q).mp hq,
    diskRadial_phase t ht (sgn b) (norm_sgn b)]

lemma sphereChartRadial_signedDomain (t : ℝ) (ht : 0 ≤ t) (k : ℕ) (b1 b0 : Bool)
    {q : SphericalSlitNeumannSpace k} (hq : q ∈ sphericalSignedDomain k b1 b0) :
    sphereChartRadial t ht (isOpen_boundaryArc k 1) q ∈ sphericalSignedDomain k b1 b0 := by
  have hc : ‖sgn b1 * sgn b0‖ = 1 := by rw [norm_mul, norm_sgn, norm_sgn, one_mul]
  exact ⟨sphereChartRadial_phase t ht k _ hc hq.1,
    sphereChartRadial_reflectionDomain t ht k b1 hq.2⟩

lemma sphereChartRadial_signedSector (t : ℝ) (ht : 0 ≤ t) (k : ℕ) (b1 b0 : Bool)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1)
    (d : ℂ) (hd : ‖d‖ = 1) {q : SphericalSlitNeumannSpace k}
    (hq : q ∈ signedSphereSectorDomain k b1 b0 θ hθ d) :
    sphereChartRadial t ht (isOpen_boundaryArc k 1) q ∈
      signedSphereSectorDomain k b1 b0 θ hθ d :=
  ⟨sphereChartRadial_signedDomain t ht k b1 b0 hq.1,
    sphereChartRadial_character t ht _ θ hθ d hd hq.2⟩

/-- Bounded chart values are dense inside the actual signed spherical character domain. -/
theorem exists_signed_sphere_bounded_approx (k : ℕ) (b1 b0 : Bool)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1)
    (d : ℂ) (hd : ‖d‖ = 1) (q : SphericalSlitNeumannSpace k)
    (hq : q ∈ signedSphereSectorDomain k b1 b0 θ hθ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : SphericalSlitNeumannSpace k, ∃ M : ℝ,
      v ∈ signedSphereSectorDomain k b1 b0 θ hθ d ∧ 0 < M ∧ ‖v - q‖ < ε ∧
      (∀ᵐ z ∂volume.restrict disk,
        ‖valueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) v).1 z‖ ≤ M) ∧
      (∀ᵐ z ∂volume.restrict disk,
        ‖valueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) v).2 z‖ ≤ M) := by
  have ht (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hc := sphereChartRadial_tendsto (fun n => (ht n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat (isOpen_boundaryArc k 1) q
  obtain ⟨n, hn⟩ := (Metric.tendsto_nhds.mp hc ε hε).exists
  refine ⟨sphereChartRadial _ (ht n).le _ q, (Real.sqrt (1 / ((n : ℝ) + 1)))⁻¹,
    sphereChartRadial_signedSector _ (ht n).le k b1 b0 θ hθ d hd hq,
    inv_pos.mpr (Real.sqrt_pos.mpr (ht n)), ?_, ?_, ?_⟩
  · simpa only [dist_eq_norm] using hn
  · rw [sphereChartRadial_coordinates]
    exact diskRadial_bounded (ht n) _
  · rw [sphereChartRadial_coordinates]
    exact diskRadial_bounded (ht n) _

end KsIndex.Spherical
