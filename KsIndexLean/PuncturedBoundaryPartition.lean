module

public import KsIndexLean.CompactBoundaryPartition
public import KsIndexLean.SlitSeamGauges

@[expose] public section


open Set Filter Topology Metric
open scoped ContDiff BigOperators
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket KsIndex.WeakH1 KsIndex.Surface

/-- The compact part of the boundary left after removing an open puncture neighborhood. -/
def boundaryAway (H : Set ℂ) : Set ℂ := sphere (0 : ℂ) 1 \ H

lemma boundaryAway_compact {H : Set ℂ} (hH : IsOpen H) : IsCompact (boundaryAway H) :=
  (isCompact_sphere (0 : ℂ) 1).diff hH

lemma arc_mem_seamDomain {k n : ℕ} {p : ℂ} (hp : p ∈ arc k n) :
    p ∈ seamDomain (boundaryArc k n) (isOpen_boundaryArc k n) := by
  apply (mem_seamDomain_iff (isOpen_boundaryArc k n) p).mpr
  refine ⟨?_, ?_⟩
  · change (1 / 2 : ℝ) < ‖p‖ ∧ ‖p‖ < 2
    rw [hp.1]
    norm_num
  · intro w hw
    change (w : ℂ) ∈ arc k n
    rwa [hw]

/-- Actual finite boundary pieces choose one of the paper's two seam domains. -/
theorem exists_punctured_boundary_partition (k : ℕ) {H : Set ℂ} (hH : IsOpen H)
    (hpH : punctures k ⊆ H) :
    ∃ t : Finset (boundaryAway H), ∃ a : boundaryAway H → ℕ,
      (∀ i, a i = 0 ∨ a i = 1) ∧ ∃ ρ : boundaryAway H → ℂ → ℝ,
      (∀ i, ContDiff ℝ ∞ (ρ i)) ∧ (∀ i, HasCompactSupport (ρ i)) ∧
      (∀ i, tsupport (ρ i) ⊆ seamDomain (boundaryArc k (a i))
        (isOpen_boundaryArc k (a i))) ∧
      (∀ i z, ρ i (σ z) = ρ i z) ∧
      ∀ p : ℂ, ‖p‖ = 1 → p ∉ H →
        (fun z => ∑ i ∈ t, ρ i z) =ᶠ[𝓝 p] 1 := by
  classical
  have hcircle (p : boundaryAway H) : ‖(p : ℂ)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp p.property.1
  have hex (p : boundaryAway H) : ∃ n : ℕ, (n = 0 ∨ n = 1) ∧
      (p : ℂ) ∈ seamDomain (boundaryArc k n) (isOpen_boundaryArc k n) := by
    have hp : (p : ℂ) ∉ punctures k := fun h => p.property.2 (hpH h)
    rcases KsIndex.SurfaceForm.mem_arc_of_not_puncture (hcircle p) hp with h | h
    · exact ⟨0, Or.inl rfl, arc_mem_seamDomain h⟩
    · exact ⟨1, Or.inr rfl, arc_mem_seamDomain h⟩
  choose a ha hm using hex
  obtain ⟨t, ρ, hc, hcomp, hs, hi, hone⟩ :=
    exists_compact_boundary_partition (boundaryAway_compact hH)
      (fun p hp => hcircle ⟨p, hp⟩)
      (fun p => (seamDomain (boundaryArc k (a p)) (isOpen_boundaryArc k (a p)) : Set ℂ))
      (fun p => (seamDomain (boundaryArc k (a p)) (isOpen_boundaryArc k (a p))).isOpen) hm
  refine ⟨t, a, ha, ρ, hc, hcomp, hs, hi, ?_⟩
  intro p hp hn
  exact hone p ⟨mem_sphere_zero_iff_norm.mpr hp, hn⟩

end KsIndex.Trace
