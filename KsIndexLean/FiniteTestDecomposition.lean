module

public import KsIndexLean.SeamDomainLocal
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

@[expose] public section


open Set MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Manifold

noncomputable section
namespace KsIndex.Trace

/-- A finite smooth partition decomposes a genuine test into genuine locally supported tests. -/
theorem finite_test_decomposition {ι : Type*} [Fintype ι]
    (U : ι → Opens ℂ) {Ω : Opens ℂ} (φ : 𝓓(Ω, ℝ))
    (hcover : tsupport (φ : ℂ → ℝ) ⊆ ⋃ i, (U i : Set ℂ)) :
    ∃ ψ : ∀ i, 𝓓(U i, ℝ), (φ : ℂ → ℝ) = fun z => ∑ i, ψ i z := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ)
    (isClosed_tsupport (φ : ℂ → ℝ)) (fun i => (U i : Set ℂ)) (fun i => (U i).isOpen) hcover
  let ψ : ∀ i, 𝓓(U i, ℝ) := fun i =>
    ⟨fun z => ρ i z * φ z, (ρ i).contMDiff.contDiff.mul φ.contDiff,
      φ.hasCompactSupport.mul_left,
      tsupport_mul_subset_left.trans (hρ i)⟩
  refine ⟨ψ, ?_⟩
  funext z
  change φ z = ∑ i, ρ i z * φ z
  rw [← Finset.sum_mul]
  by_cases hz : z ∈ tsupport (φ : ℂ → ℝ)
  · rw [← finsum_eq_sum_of_fintype, ρ.sum_eq_one hz, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]

end KsIndex.Trace
