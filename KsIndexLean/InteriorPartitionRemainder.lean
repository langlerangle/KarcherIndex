module

public import KsIndexLean.CompactBoundaryPartition
public import KsIndexLean.WeakH1Adapter

@[expose] public section


open Set Filter Topology MeasureTheory Metric
open scoped BigOperators
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- A boundary partition plus AE holes gives a genuinely compact interior representative. -/
theorem exists_interior_remainder_rep {H : Set ℂ} (hH : IsOpen H)
    {u : ℂ → ℂ} {a : ℂ → ℝ}
    (hu : ∀ᵐ z ∂volume.restrict disk, z ∈ H → u z = 0)
    (ha : ∀ p : ℂ, ‖p‖ = 1 → p ∉ H → a =ᶠ[𝓝 p] 1) :
    ∃ v : ℂ → ℂ, HasCompactSupport v ∧ tsupport v ⊆ disk ∧
      v =ᵐ[volume.restrict disk] (fun z => (1 - a z) • u z) := by
  classical
  let V : Set ℂ := H ∪ interior {z | a z = 1}
  have hV : IsOpen V := hH.union isOpen_interior
  have hcircle : ∀ p : ℂ, ‖p‖ = 1 → p ∈ V := by
    intro p hp
    by_cases hh : p ∈ H
    · exact Or.inl hh
    · exact Or.inr (mem_interior_iff_mem_nhds.mpr (ha p hp hh))
  let K : Set ℂ := closedBall (0 : ℂ) 1 \ V
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).diff hV
  have hKd : K ⊆ disk := by
    intro z hz
    apply KsIndex.SurfaceForm.mem_disk_iff.mpr
    have hn : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz.1
    exact lt_of_le_of_ne hn (fun he => hz.2 (hcircle z he))
  let v : ℂ → ℂ := K.indicator (fun z => (1 - a z) • u z)
  have hs : tsupport v ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_contra hn
    exact hz (by simp [v, hn])
  refine ⟨v, hK.of_isClosed_subset isClosed_closure hs, hs.trans hKd, ?_⟩
  filter_upwards [hu, ae_restrict_mem KsIndex.SurfaceForm.measurableSet_disk] with z hz hzd
  by_cases hv : z ∈ V
  · have hzero : (1 - a z) • u z = 0 := by
      rcases hv with hh | hh
      · rw [hz hh, smul_zero]
      · have he : z ∈ {w | a w = 1} := interior_subset hh
        rw [he, sub_self, zero_smul]
    have hk : z ∉ K := fun h => h.2 hv
    simp [v, hk, hzero]
  · have hk : z ∈ K := by
      refine ⟨?_, hv⟩
      have hn := (KsIndex.SurfaceForm.mem_disk_iff.mp hzd).le
      simpa only [mem_closedBall, dist_zero_right] using hn
    simp [v, hk]

/-- The compact interior representative plus the boundary contribution recovers the input. -/
lemma interior_remainder_reconstruction {u v : ℂ → ℂ} {a : ℂ → ℝ}
    (hv : v =ᵐ[volume.restrict disk] (fun z => (1 - a z) • u z)) :
    (fun z => v z + a z • u z) =ᵐ[volume.restrict disk] u := by
  filter_upwards [hv] with z hz
  rw [hz, ← add_smul]
  simp

/-- A finite boundary partition yields an interior representative and exact AE reconstruction. -/
theorem finite_partition_interior_remainder {ι : Type*} (t : Finset ι)
    (ρ : ι → ℂ → ℝ) {H : Set ℂ} (hH : IsOpen H) {u : ℂ → ℂ}
    (hu : ∀ᵐ z ∂volume.restrict disk, z ∈ H → u z = 0)
    (hρ : ∀ p : ℂ, ‖p‖ = 1 → p ∉ H →
      (fun z => ∑ i ∈ t, ρ i z) =ᶠ[𝓝 p] 1) :
    ∃ v : ℂ → ℂ, HasCompactSupport v ∧ tsupport v ⊆ disk ∧
      v =ᵐ[volume.restrict disk] (fun z => (1 - ∑ i ∈ t, ρ i z) • u z) ∧
      (fun z => v z + ∑ i ∈ t, ρ i z • u z) =ᵐ[volume.restrict disk] u := by
  obtain ⟨v, hc, hs, hv⟩ := exists_interior_remainder_rep hH hu hρ
  refine ⟨v, hc, hs, hv, ?_⟩
  simpa only [Finset.sum_smul] using interior_remainder_reconstruction hv

end KsIndex.Trace
