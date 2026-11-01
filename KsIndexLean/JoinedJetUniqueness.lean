module

public import KsIndexLean.SeamDomainWeakGluing
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section


open Set MeasureTheory TopologicalSpace

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma ae_norm_ne_one : ∀ᵐ z : ℂ ∂volume, ‖z‖ ≠ 1 := by
  have h := (show volume (Metric.sphere (0 : ℂ) 1) = 0 from Measure.addHaar_sphere volume 0 1)
  have he := (compl_mem_ae_iff.mpr h : ∀ᵐ z : ℂ ∂volume, z ∉ Metric.sphere 0 1)
  filter_upwards [he] with z hz
  exact fun hn => hz (mem_sphere_zero_iff_norm.mpr hn)

/-- An already-existing weak jet is determined off the null middle circle by the two collars. -/
theorem joinedDiskJet_unique {Ω : Opens ℂ} (hΩ : (Ω : Set ℂ) ⊆ annulusSet (1 / 2 : ℝ) 2)
    (u v : ComplexH1) (c : ℂ) {J : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume Ω (joinedDiskValue u v c) J) :
    J =ᵐ[volume.restrict (Ω : Set ℂ)] joinedDiskJet u v c := by
  have h1 := (hw.mono (show Ω ⊓ annulusOpens (1 / 2) 1 ≤ Ω from inf_le_left)).ae_eq
    ((uncut_inner_collar_weak u v c).mono inf_le_right)
  have h2 := (hw.mono (show Ω ⊓ annulusOpens 1 2 ≤ Ω from inf_le_left)).ae_eq
    ((uncut_outer_collar_weak u v c).mono inf_le_right)
  apply (ae_restrict_iff' Ω.isOpen.measurableSet).mpr
  filter_upwards [(ae_restrict_iff' (Ω ⊓ annulusOpens (1 / 2) 1).isOpen.measurableSet).mp h1,
    (ae_restrict_iff' (Ω ⊓ annulusOpens 1 2).isOpen.measurableSet).mp h2,
    ae_norm_ne_one] with z hz1 hz2 hn hz
  have ha := hΩ hz
  rcases lt_or_gt_of_ne hn with hn | hn
  · exact hz1 ⟨hz, ha.1, hn⟩
  · exact hz2 ⟨hz, hn, ha.2⟩

/-- Existence of any weak jet is equivalent to regularity with the explicit jet. -/
theorem joinedDisk_weak_exists_iff {Ω : Opens ℂ}
    (hΩ : (Ω : Set ℂ) ⊆ annulusSet (1 / 2 : ℝ) 2) (u v : ComplexH1) (c : ℂ) :
    (∃ J, TauCeti.HasWeakFDerivOn volume Ω (joinedDiskValue u v c) J) ↔
      TauCeti.HasWeakFDerivOn volume Ω (joinedDiskValue u v c) (joinedDiskJet u v c) := by
  constructor
  · rintro ⟨J, hJ⟩
    exact hJ.congr_ae_deriv (joinedDiskJet_unique hΩ u v c hJ)
  · intro h
    exact ⟨_, h⟩

lemma joinedDisk_weak_jet_memLp {Ω : Opens ℂ}
    (hΩ : (Ω : Set ℂ) ⊆ annulusSet (1 / 2 : ℝ) 2)
    (u v : ComplexH1) (c : ℂ) {J : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume Ω (joinedDiskValue u v c) J) :
    MemLp J 2 (volume.restrict (Ω : Set ℂ)) :=
  MemLp.ae_eq (joinedDiskJet_unique hΩ u v c hw).symm
    ((memLp_joinedDiskJet u v c).mono_measure (Measure.restrict_mono hΩ le_rfl))

end KsIndex.Trace
