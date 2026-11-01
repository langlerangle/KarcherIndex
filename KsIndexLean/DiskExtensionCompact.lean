module

public import KsIndexLean.DiskComplexTranslation
public import TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov

@[expose] public section


noncomputable section
open Set MeasureTheory TopologicalSpace TauCeti
open scoped ENNReal
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Whole-plane L2 realization of the compactly supported disk extension. -/
def diskExtensionLp (u : ComplexH1) : Lp ℂ 2 (volume : Measure ℂ) :=
  (cutoffDiskExtension_spec u).2.1.toLp (cutoffDiskExtension u)

lemma diskExtensionLp_ae (u : ComplexH1) :
    diskExtensionLp u =ᵐ[volume] cutoffDiskExtension u :=
  (cutoffDiskExtension_spec u).2.1.coeFn_toLp

lemma diskExtensionLp_norm_sq (u : ComplexH1) :
    ‖diskExtensionLp u‖ ^ 2 = ∫ z : ℂ, ‖cutoffDiskExtension u z‖ ^ 2 := by
  have he := L2.inner_def (𝕜 := ℝ) (diskExtensionLp u) (diskExtensionLp u)
  simp only [real_inner_self_eq_norm_sq] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [diskExtensionLp_ae u] with z hz
  rw [hz]

/-- Relative L2 compactness of the extensions of the full disk H1 unit ball. -/
theorem diskExtensionLp_unitBall_relativelyCompact :
    IsCompact (closure (diskExtensionLp '' {u : ComplexH1 | ‖u‖ ≤ 1})) := by
  obtain ⟨K, hK, hbound⟩ := cutoffDiskExtension_uniform_energy
  apply isCompact_closure_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (s := Metric.ball (0 : ℂ) 2)
    Metric.isBounded_ball
  · rintro f ⟨u, hu, rfl⟩
    filter_upwards [diskExtensionLp_ae u] with z hz
    intro hout
    rw [hz, cutoffDiskExtension_zero_outside u hout]
  · exact ENNReal.ofReal_ne_top (r := K + 1)
  · rintro f ⟨u, hu, rfl⟩
    have hu2 : ‖u‖ ^ 2 ≤ 1 := by
      change ‖u‖ ≤ 1 at hu
      nlinarith [norm_nonneg u]
    have hx : 0 ≤ ∫ z : ℂ, ‖cutoffDiskExtensionJet u z 1‖ ^ 2 :=
      integral_nonneg (fun z => sq_nonneg _)
    have hy : 0 ≤ ∫ z : ℂ, ‖cutoffDiskExtensionJet u z Complex.I‖ ^ 2 :=
      integral_nonneg (fun z => sq_nonneg _)
    have hsq : ‖diskExtensionLp u‖ ^ 2 ≤ K := by
      rw [diskExtensionLp_norm_sq]
      have hk := mul_le_mul_of_nonneg_left hu2 hK
      linarith [hbound u]
    have hn : ‖diskExtensionLp u‖ ≤ K + 1 := by nlinarith [sq_nonneg K]
    rw [← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_mono hn
  · intro ε hε
    obtain ⟨δ, hδ, ht⟩ := diskExtension_unitBall_small_translations hε
    refine ⟨δ, hδ, ?_⟩
    rintro f ⟨u, hu, rfl⟩ h hh
    have hv := diskExtensionLp_ae u
    have hvh := hv.comp_tendsto
      (measurePreserving_add_right (volume : Measure ℂ) h).quasiMeasurePreserving.tendsto_ae
    have he : eLpNorm (fun z => diskExtensionLp u (z + h) - diskExtensionLp u z) 2 volume =
        eLpNorm (fun z => cutoffDiskExtension u (z + h) - cutoffDiskExtension u z) 2 volume := by
      apply eLpNorm_congr_ae
      filter_upwards [hv, hvh] with z hz hzh
      dsimp only [Function.comp_apply] at hzh
      rw [hz, hzh]
    rw [he]
    exact ht u hu h hh

end KsIndex.Trace
