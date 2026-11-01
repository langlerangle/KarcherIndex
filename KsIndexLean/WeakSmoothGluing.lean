module

public import KsIndexLean.WeakInteriorSmooth

@[expose] public section


/-! Smooth representatives agree on open overlaps and therefore assemble to
one representative on the coordinate domain. Countability is used only to
pass from local almost-everywhere equality to almost-everywhere equality on Ω. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Weq

/-- Local smooth representatives of one measurable class assemble on the whole
open domain. Values outside the domain carry no mathematical assertion. -/
theorem exists_contDiffOn_ae_of_smooth_near {Ω : Set ℂ} {u : ℂ → ℂ}
    (h : ∀ z ∈ Ω, ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ Ω ∧ ∃ g : ℂ → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧ u =ᵐ[volume.restrict (Metric.ball z r)] g) :
    ∃ F : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F Ω ∧ u =ᵐ[volume.restrict Ω] F := by
  classical
  choose r hr hs g hg ha using fun z : Ω => h z z.property
  let B (z : Ω) := Metric.ball (z : ℂ) (r z)
  let F (x : ℂ) := if hx : x ∈ Ω then g ⟨x, hx⟩ x else 0
  have hmatch (a : Ω) : EqOn F (g a) (B a) := by
    intro x hx
    have hxΩ : x ∈ Ω := hs a hx
    let b : Ω := ⟨x, hxΩ⟩
    have hax : u =ᵐ[volume.restrict (B a ∩ B b)] g a :=
      (ha a).filter_mono (ae_mono (Measure.restrict_mono inter_subset_left le_rfl))
    have hbx : u =ᵐ[volume.restrict (B a ∩ B b)] g b :=
      (ha b).filter_mono (ae_mono (Measure.restrict_mono inter_subset_right le_rfl))
    have he : EqOn (g b) (g a) (B a ∩ B b) :=
      Measure.eqOn_open_of_ae_eq (hbx.symm.trans hax)
        (Metric.isOpen_ball.inter Metric.isOpen_ball)
        (hg b).continuous.continuousOn (hg a).continuous.continuousOn
    have hb : x ∈ B b := Metric.mem_ball_self (hr b)
    simpa only [F, dite_eq_left hxΩ] using he ⟨hx, hb⟩
  refine ⟨F, ?_, ?_⟩
  · intro x hx
    let a : Ω := ⟨x, hx⟩
    have hev : F =ᶠ[nhds x] g a := by
      filter_upwards [Metric.ball_mem_nhds x (hr a)] with y hy
      exact hmatch a hy
    exact ((hg a).contDiffAt.congr_of_eventuallyEq hev).contDiffWithinAt
  · have hcover : (⋃ a : Ω, B a) = Ω := by
      apply Subset.antisymm
      · exact iUnion_subset fun a => hs a
      · intro x hx
        exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩
    obtain ⟨T, hT, hTc⟩ := TopologicalSpace.isOpen_iUnion_countable B (fun _ => Metric.isOpen_ball)
    have he : (⋃ a ∈ T, B a) = Ω := hTc.trans hcover
    rw [← he, ae_eq_restrict_biUnion_iff B hT]
    intro a _
    filter_upwards [ha a, ae_restrict_mem measurableSet_ball] with x hx hxb
    exact hx.trans (hmatch a hxb).symm

end KsIndex.Weq
