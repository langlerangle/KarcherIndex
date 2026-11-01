module

public import KsIndexLean.UncutCollarRegions

@[expose] public section


open Set MeasureTheory TopologicalSpace

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- The annulus with the unmatched portion of its middle circle removed. -/
def seamDomain (A : Set Circle₁) (hA : IsOpen A) : Opens ℂ :=
  ⟨annulusSet (1 / 2 : ℝ) 2 \ Subtype.val '' Aᶜ,
    (annulusOpens (1 / 2) 2).isOpen.sdiff
      ((hA.isClosed_compl.isCompact.image continuous_subtype_val).isClosed)⟩

/-- A single explicit jet is a local weak derivative everywhere in the matching seam domain. -/
theorem seamDomain_local_weak {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) (hm : arcTrace A u = c • arcTrace A v)
    {z : ℂ} (hz : z ∈ seamDomain A hA) :
    ∃ Ω : Opens ℂ, z ∈ Ω ∧ Ω ≤ seamDomain A hA ∧
      TauCeti.HasWeakFDerivOn volume Ω (joinedDiskValue u v c) (joinedDiskJet u v c) := by
  have hza : z ∈ annulusSet (1 / 2 : ℝ) 2 := hz.1
  have hex : ∃ Ω : Opens ℂ, z ∈ Ω ∧
      TauCeti.HasWeakFDerivOn volume Ω (joinedDiskValue u v c) (joinedDiskJet u v c) := by
    by_cases hn : ‖z‖ = 1
    · have hs : z ∈ Circle₁ := by simpa using hn
      let w : Circle₁ := ⟨z, hs⟩
      have hw : w ∈ A := by
        by_contra h
        exact hz.2 ⟨w, h, rfl⟩
      obtain ⟨Ω, hΩz, _, hΩ⟩ := local_uncut_disk_gluing hA u v c hm hw
      exact ⟨Ω, hΩz, hΩ⟩
    · rcases lt_or_gt_of_ne hn with hlt | hgt
      · exact ⟨annulusOpens (1 / 2) 1, ⟨hza.1, hlt⟩, uncut_inner_collar_weak u v c⟩
      · exact ⟨annulusOpens 1 2, ⟨hgt, hza.2⟩, uncut_outer_collar_weak u v c⟩
  obtain ⟨Ω, hΩz, hΩ⟩ := hex
  exact ⟨Ω ⊓ seamDomain A hA, ⟨hΩz, hz⟩, inf_le_right, hΩ.mono inf_le_left⟩

end KsIndex.Trace
