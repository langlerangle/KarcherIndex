module

public import KsIndexLean.PhaseGermInteriorSmooth

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket

/-- Swapping the two ordinary gluing germs agrees with inversion off the
null seam and origin, for arbitrary representatives. -/
lemma phaseGerm_one_inversion_ae (f g : ℂ → ℂ) :
    (fun z => phaseGerm 1 f g (σ z)) =ᵐ[volume] phaseGerm 1 g f := by
  filter_upwards [volume.ae_ne (0 : ℂ), ae_norm_ne_one] with z hz hn
  simp only [phaseGerm, one_mul, σ_σ]
  rcases lt_or_gt_of_ne hn with h | h
  · rw [ite_eq_right (not_norm_σ_le hz h), ite_eq_left h.le]
  · have hi : ‖σ z‖ ≤ 1 := by
      rw [norm_σ]
      exact (inv_le_one₀ (norm_pos_iff.mpr hz)).mpr h.le
    rw [ite_eq_left hi, ite_eq_right (not_le.mpr h)]

/-- Smooth ordinary germs agree pointwise on their chart overlap, including
uncut equator points. AE agreement is upgraded using open-positive volume. -/
theorem phaseGerm_one_inversion_eq (f g : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0)
    (hf : ContDiffAt ℝ ∞ (phaseGerm 1 f g) (σ z))
    (hg : ContDiffAt ℝ ∞ (phaseGerm 1 g f) z) :
    phaseGerm 1 f g (σ z) = phaseGerm 1 g f z := by
  have hc := hf.comp z (contDiffAt_σ hz)
  obtain ⟨U, hU, hzU, hcU⟩ := continuous_neighbourhood_of_smooth_germ hc
  obtain ⟨V, hV, hzV, hcV⟩ := continuous_neighbourhood_of_smooth_germ hg
  exact Measure.eqOn_open_of_ae_eq
    (ae_restrict_of_ae (phaseGerm_one_inversion_ae f g)) (hU.inter hV)
    (hcU.mono inter_subset_left) (hcV.mono inter_subset_right) ⟨hzU, hzV⟩

/-- At an uncut equator point, compatible smooth germs have equal values. -/
lemma phaseGerm_one_boundary_eq (f g : ℂ → ℂ) {z : ℂ} (hz : ‖z‖ = 1)
    (hf : ContDiffAt ℝ ∞ (phaseGerm 1 f g) z)
    (hg : ContDiffAt ℝ ∞ (phaseGerm 1 g f) z) : f z = g z := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have hs := σ_self hz
  have he := phaseGerm_one_inversion_eq f g hz0 (by simpa only [hs] using hf) hg
  simpa [hs, phaseGerm, hz] using he

/-- A common hole in both hemisphere functions gives a zero germ at a
circle puncture, including the inverted side of the chart. -/
lemma phaseGerm_zero_near (c : ℂ) {f g : ℂ → ℂ} {q : ℂ} (hq : ‖q‖ = 1)
    (hf : f =ᶠ[𝓝 q] 0) (hg : g =ᶠ[𝓝 q] 0) :
    phaseGerm c f g =ᶠ[𝓝 q] 0 := by
  have hq0 : q ≠ 0 := norm_ne_zero_iff.mp (by rw [hq]; norm_num)
  have ht : Tendsto σ (𝓝 q) (𝓝 q) := by
    simpa only [σ_self hq] using (continuousAt_σ hq0).tendsto
  filter_upwards [hf, ht.eventually hg] with z hz hi
  simp [phaseGerm, hz, hi]

end KsIndex.Trace
