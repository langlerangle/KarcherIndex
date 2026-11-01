module

public import KsIndexLean.PolarJetInverse
public import KsIndexLean.WeakLocality
public import KsIndexLean.SeamWeakTraceEquivalence

@[expose] public section


open Set MeasureTheory TopologicalSpace

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- A radius-two chart retaining the first disk and the matching middle-circle arcs. -/
def extendedSeamDomain (A : Set Circle₁) (hA : IsOpen A) : Opens ℂ :=
  ⟨Metric.ball 0 2 \ Subtype.val '' Aᶜ,
    Metric.isOpen_ball.sdiff
      ((hA.isClosed_compl.isCompact.image continuous_subtype_val).isClosed)⟩

lemma seamDomain_le_extended {A : Set Circle₁} (hA : IsOpen A) :
    seamDomain A hA ≤ extendedSeamDomain A hA := by
  intro z hz
  exact ⟨by simpa [Metric.mem_ball, dist_zero_right] using hz.1.2, hz.2⟩

lemma disk_le_extendedSeamDomain {A : Set Circle₁} (hA : IsOpen A) :
    disk ≤ extendedSeamDomain A hA := by
  intro z hz
  have hn : ‖z‖ < 1 := by simpa [disk, Metric.mem_ball, dist_zero_right] using hz
  refine ⟨?_, ?_⟩
  · simpa [Metric.mem_ball, dist_zero_right] using hn.trans (by norm_num : (1 : ℝ) < 2)
  · rintro ⟨w, _, he⟩
    have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
    rw [he] at hw
    linarith

theorem extendedSeamDomain_weak {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) (hm : arcTrace A u = c • arcTrace A v) :
    TauCeti.HasWeakFDerivOn volume (extendedSeamDomain A hA)
      (joinedDiskValue u v c) (joinedDiskJet u v c) := by
  apply weakF_of_weak_neighborhoods
  intro z hz
  by_cases hn : ‖z‖ < 1
  · exact ⟨disk, by simpa [disk, Metric.mem_ball, dist_zero_right] using hn,
      joinedDisk_inner_disk_weak u v c⟩
  · have h2 : ‖z‖ < 2 := by simpa [Metric.mem_ball, dist_zero_right] using hz.1
    have h1 : (1 / 2 : ℝ) < ‖z‖ := by linarith [not_lt.mp hn]
    exact ⟨seamDomain A hA, ⟨⟨h1, h2⟩, hz.2⟩, seamDomain_weak_gluing hA u v c hm⟩

/-- The chart including the disk center has exactly the same genuine trace criterion. -/
theorem extendedSeamDomain_weak_iff_trace {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) :
    (∃ J, TauCeti.HasWeakFDerivOn volume (extendedSeamDomain A hA) (joinedDiskValue u v c) J) ↔
      arcTrace A u = c • arcTrace A v := by
  constructor
  · rintro ⟨J, hJ⟩
    exact (seamDomain_weak_iff_trace hA u v c).mp ⟨J, hJ.mono (seamDomain_le_extended hA)⟩
  · intro hm
    exact ⟨_, extendedSeamDomain_weak hA u v c hm⟩

end KsIndex.Trace
