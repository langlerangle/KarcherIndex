module

public import KsIndexLean.FullBoundaryReflection

@[expose] public section


noncomputable section
open Set MeasureTheory TopologicalSpace
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk

/-- Cartesian near the center, reflected polar derivative outside the unit disk. -/
def diskExtensionJet (u : ComplexH1) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  if ‖z‖ < 1 then Dxy (dxLp u) (dyLp u) z else joinedDiskJet u u 1 z

lemma diskExtensionJet_inner (u : ComplexH1) :
    Dxy (dxLp u) (dyLp u) =ᵐ[volume.restrict (disk : Set ℂ)] diskExtensionJet u := by
  filter_upwards [ae_restrict_mem disk.isOpen.measurableSet] with z hz
  simp only [diskExtensionJet, ite_eq_left (KsIndex.SurfaceForm.mem_disk_iff.mp hz)]

lemma diskExtensionJet_annulus (u : ComplexH1) :
    joinedDiskJet u u 1 =ᵐ[volume.restrict (annulusSet (1 / 2 : ℝ) 2)] diskExtensionJet u := by
  have he := (ae_restrict_iff' (measurableSet_annulusSet (a := 1 / 2) (b := 1))).mp
    (full_boundary_even_jet_overlap u)
  apply (ae_restrict_iff' (measurableSet_annulusSet (a := 1 / 2) (b := 2))).mpr
  filter_upwards [he] with z hz ha
  by_cases hi : ‖z‖ < 1
  · simp only [diskExtensionJet, ite_eq_left hi]
    exact (hz ⟨ha.1, hi⟩).symm
  · simp only [diskExtensionJet, ite_eq_right hi]

/-- Local weak differentiability on an open cover already supplies local integrability. -/
theorem weakF_of_open_local {Ω : Opens ℂ} {f : ℂ → ℂ} {J : ℂ → ℂ →L[ℝ] ℂ}
    (h : ∀ z ∈ Ω, ∃ V : Opens ℂ, z ∈ V ∧ TauCeti.HasWeakFDerivOn volume V f J) :
    TauCeti.HasWeakFDerivOn volume Ω f J := by
  apply weakF_of_local _ _ h
  · intro z hz
    obtain ⟨V, hzV, hw⟩ := h z hz
    have hi := (hw.hasWeakLineDerivOn 1).locallyIntegrableOn z hzV
    rw [V.isOpen.nhdsWithin_eq hzV] at hi
    exact hi.filter_mono nhdsWithin_le_nhds
  · intro d z hz
    obtain ⟨V, hzV, hw⟩ := h z hz
    have hi := (hw.hasWeakLineDerivOn d).locallyIntegrableOn_deriv z hzV
    rw [V.isOpen.nhdsWithin_eq hzV] at hi
    exact hi.filter_mono nhdsWithin_le_nhds

/-- Unrestricted even reflection is weak H1 across the boundary and through the center. -/
theorem disk_reflection_extension_weak (u : ComplexH1) :
    TauCeti.HasWeakFDerivOn volume (disk ⊔ annulusOpens (1 / 2) 2)
      (refl 1 (valueCLM u)) (diskExtensionJet u) := by
  apply weakF_of_open_local
  intro z hz
  rcases hz with hi | ho
  · exact ⟨disk, hi, (full_boundary_even_inner_weak u).congr_ae_deriv
      (diskExtensionJet_inner u)⟩
  · exact ⟨annulusOpens (1 / 2) 2, ho, (full_boundary_even_extension u).congr_ae_deriv
      (diskExtensionJet_annulus u)⟩

/-- The two extension regions cover precisely the radius-two disk. -/
lemma disk_union_reflection_annulus :
    ((disk ⊔ annulusOpens (1 / 2) 2 : Opens ℂ) : Set ℂ) = Metric.ball 0 2 := by
  ext z
  change (z ∈ Metric.ball (0 : ℂ) 1 ∨ (1 / 2 : ℝ) < ‖z‖ ∧ ‖z‖ < 2) ↔ _
  simp only [Metric.mem_ball, dist_zero_right]
  constructor
  · rintro (h | h)
    · linarith
    · exact h.2
  · intro h
    by_cases hi : ‖z‖ < 1
    · exact Or.inl hi
    · exact Or.inr ⟨by linarith, h⟩

end KsIndex.Trace
