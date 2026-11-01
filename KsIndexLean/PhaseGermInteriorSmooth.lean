module

public import KsIndexLean.PhasePairMollification

@[expose] public section


open Set Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket KsIndex.SingleDisk

/-- Near the center of either disk chart the gluing germ is its smooth
interior representative, so no inversion singularity is encountered. -/
lemma phaseGerm_contDiffAt_inside (c : ℂ) {f g : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) {z : ℂ} (hz : ‖z‖ < 1) :
    ContDiffAt ℝ ∞ (phaseGerm c (closedDiskRestriction f)
      (closedDiskRestriction g)) z := by
  have he : phaseGerm c (closedDiskRestriction f) (closedDiskRestriction g)
      =ᶠ[𝓝 z] f := by
    filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hz)] with w hw
    simp [phaseGerm, closedDiskRestriction, hw.le]
  exact hf.contDiffAt.congr_of_eventuallyEq he

/-- Outside the unit circle the smooth gluing germ uses only inversion away
from zero and evaluates the second representative strictly inside its disk. -/
lemma phaseGerm_contDiffAt_outside (c : ℂ) {f g : ℂ → ℂ}
    (hg : ContDiff ℝ ∞ g) {z : ℂ} (hz : 1 < ‖z‖) :
    ContDiffAt ℝ ∞ (phaseGerm c (closedDiskRestriction f)
      (closedDiskRestriction g)) z := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hz)
  have he : phaseGerm c (closedDiskRestriction f) (closedDiskRestriction g)
      =ᶠ[𝓝 z] (fun w => c * g (σ w)) := by
    filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hz)] with w hw
    have hi : ‖σ w‖ ≤ 1 := by
      rw [norm_σ]
      exact (inv_le_one₀ (zero_lt_one.trans hw)).mpr hw.le
    simp [phaseGerm, closedDiskRestriction, not_le.mpr hw, hi]
  exact (contDiffAt_const.mul (hg.contDiffAt.comp z (contDiffAt_σ hz0))).congr_of_eventuallyEq he

/-- Smoothness on the planar slit-sphere chart follows from interior
smoothness and the ordinary (phase-one) germ on the uncut equator. -/
theorem phaseGerm_contDiffOn_slit_compl (k : ℕ) {f g : ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hseam : ∀ z ∈ KsIndex.Surface.arc k 1,
      ContDiffAt ℝ ∞ (phaseGerm 1 (closedDiskRestriction f)
        (closedDiskRestriction g)) z) :
    ContDiffOn ℝ ∞ (phaseGerm 1 (closedDiskRestriction f)
      (closedDiskRestriction g)) (slit k)ᶜ := by
  intro z hz
  rcases lt_trichotomy ‖z‖ 1 with h | h | h
  · exact (phaseGerm_contDiffAt_inside 1 hf h).contDiffWithinAt
  · have hp : 0 < (z ^ k).re := by
      by_contra hn
      exact hz ⟨h, le_of_not_gt hn⟩
    have ha : z ∈ KsIndex.Surface.arc k 1 := by
      change ‖z‖ = 1 ∧ (-1 : ℝ) ^ 1 * (z ^ k).re < 0
      exact ⟨h, by simpa using neg_neg_of_pos hp⟩
    exact (hseam z ha).contDiffWithinAt
  · exact (phaseGerm_contDiffAt_outside 1 hg h).contDiffWithinAt

end KsIndex.Trace
