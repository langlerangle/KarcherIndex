module

public import KsIndexLean.SphericalCutoff
public import KsIndexLean.SignedSphereSector

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

lemma sphereChartCutoff_character {k : ℕ} (hk : 1 ≤ k) (j : ℕ)
    {A : Set Circle₁} (hA : IsOpen A) (θ : ℝ) (hθ : circleRotate θ ⁻¹' A = A) (d : ℂ)
    (hroot : Complex.exp ((θ : ℂ) * Complex.I) ^ (2 * k) = 1) {q : SphereChartSpace A hA}
    (hq : q ∈ sphereChartCharacterDomain hA θ hθ d) :
    sphereChartCutoff k j hA q ∈ sphereChartCharacterDomain hA θ hθ d := by
  have h := (mem_sphereChartCharacterDomain_iff_pair hA θ hθ d q).mp hq
  rw [mem_sphereChartCharacterDomain_iff_pair, sphereChartCutoff_coordinates]
  exact ⟨diskCutoff_mem_weakCharacterDomain hk j θ d hroot h.1,
    diskCutoff_mem_weakCharacterDomain hk j θ d hroot h.2⟩

lemma sphereChartCutoff_reflectionDomain (k j : ℕ) (b : Bool)
    {q : SphericalSlitNeumannSpace k} (hq : q ∈ sphereReflectionDomain k b) :
    sphereChartCutoff k j (isOpen_boundaryArc k 1) q ∈ sphereReflectionDomain k b := by
  rw [mem_sphereReflectionDomain_iff, sphereChartCutoff_coordinates]
  rw [(mem_sphereReflectionDomain_iff k b q).mp hq, map_smul]

lemma sphereChartCutoff_signedDomain (k j : ℕ) (b1 b0 : Bool)
    {q : SphericalSlitNeumannSpace k} (hq : q ∈ sphericalSignedDomain k b1 b0) :
    sphereChartCutoff k j (isOpen_boundaryArc k 1) q ∈ sphericalSignedDomain k b1 b0 :=
  ⟨sphereChartCutoff_phase k j _ hq.1, sphereChartCutoff_reflectionDomain k j b1 hq.2⟩

lemma sphereChartCutoff_signedSector {k : ℕ} (hk : 1 ≤ k) (j : ℕ) (b1 b0 : Bool)
    (θ : ℝ) (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ)
    (hroot : Complex.exp ((θ : ℂ) * Complex.I) ^ (2 * k) = 1)
    {q : SphericalSlitNeumannSpace k} (hq : q ∈ signedSphereSectorDomain k b1 b0 θ hθ d) :
    sphereChartCutoff k j (isOpen_boundaryArc k 1) q ∈ signedSphereSectorDomain k b1 b0 θ hθ d :=
  ⟨sphereChartCutoff_signedDomain k j b1 b0 hq.1,
    sphereChartCutoff_character hk j _ θ hθ d hroot hq.2⟩

end KsIndex.Spherical
