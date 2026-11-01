module

public import KsIndexLean.InvariantPartition

@[expose] public section


open Set Filter Topology
open scoped ContDiff BigOperators
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket

/-- A genuine finite smooth invariant partition near a compact subset of the circle,
with each piece subordinate to its prescribed neighborhood. -/
theorem exists_compact_boundary_partition {K : Set ℂ} (hK : IsCompact K)
    (hcircle : ∀ p ∈ K, ‖p‖ = 1) (Ω : K → Set ℂ)
    (hΩ : ∀ p, IsOpen (Ω p)) (hpΩ : ∀ p : K, (p : ℂ) ∈ Ω p) :
    ∃ t : Finset K, ∃ ρ : K → ℂ → ℝ,
      (∀ i, ContDiff ℝ ∞ (ρ i)) ∧ (∀ i, HasCompactSupport (ρ i)) ∧
      (∀ i, tsupport (ρ i) ⊆ Ω i) ∧ (∀ i z, ρ i (σ z) = ρ i z) ∧
      ∀ p ∈ K, (fun z => ∑ i ∈ t, ρ i z) =ᶠ[𝓝 p] 1 := by
  classical
  let : LinearOrder K := linearOrderOfSTO WellOrderingRel
  have hex := fun p : K => exists_invariant_cutoff (hΩ p) (hpΩ p) (hcircle p p.property)
  choose χ hc hcompact hs hzero hi hone using hex
  have hcover : K ⊆ ⋃ i : K, interior {z | χ i z = 1} := by
    intro p hp
    apply mem_iUnion.mpr
    refine ⟨⟨p, hp⟩, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact hone ⟨p, hp⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun i : K => interior {z | χ i z = 1}) (fun _ => isOpen_interior) hcover
  refine ⟨t, invariantPartitionWeight t χ,
    invariantPartitionWeight_smooth t hc,
    fun i => invariantPartitionWeight_compact t i (hcompact i),
    fun i => (invariantPartitionWeight_support t χ i).trans (hs i),
    invariantPartitionWeight_invariant t hi, ?_⟩
  intro p hp
  obtain ⟨i, hit, hip⟩ := mem_iUnion₂.mp (ht hp)
  exact invariantPartitionWeight_sum_one_near t χ hit
    (mem_interior_iff_mem_nhds.mp hip)

end KsIndex.Trace
