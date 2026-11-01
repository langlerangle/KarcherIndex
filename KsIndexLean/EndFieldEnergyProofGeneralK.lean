module

public import KsIndexLean.EndFieldEnergyProof

@[expose] public section


/-! Derivative identities for the direct and reflected branches of an end field.

For `IsSmooth k m u`, local constancy of the copy index away from the pulled-back
unit circle allows the chain rule on each branch. The direct branch uses the
end chart; the reflected branch also composes with inversion in the unit circle.
The arguments use the disk-smoothness component of `IsSmooth` and apply for
arbitrary `k`. Both identities retain the nonzero chart-coordinate, small-radius
and strict inside/outside hypotheses. They provide derivative identities, not
a complete finite-energy or puncture-removal conclusion. -/
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped ContDiff
namespace KsIndex.EndField
open KsIndex.Surface KsIndex.EndChart KsIndex.B2 KsIndex.FaithfulInjection

lemma endField_fderiv_inside_energy_general {k m : ℕ} {u : ZMod (2*m) → ℂ → ℂ}
    (hu : IsSmooth k m u) (p : ℂ) (hp : ‖p‖ = 1) (c : ZMod (2*m))
    {z : ℂ} (hz : z ≠ 0) (hr : ‖z‖^m < 1) (hin : ‖endChart p m z‖ < 1) :
    fderiv ℝ (endFieldWith p u (endIdx m c p)) z =
      (fderiv ℝ (u (endIdx m c p z)) (endChart p m z)).comp (endDeriv m z) := by
  have hi := endIdx_locally_constant_off_circle p hp c hz hr hin.ne
  have hEc : ContinuousAt (fun w => ‖endChart p m w‖) z := by
    unfold endChart
    fun_prop
  have heq : endFieldWith p u (endIdx m c p) =ᶠ[𝓝 z]
      (fun w => u (endIdx m c p z) (endChart p m w)) := by
    filter_upwards [hi, hEc.eventually (gt_mem_nhds hin)] with w hw hwin
    rw [endFieldWith_inside p u _ hwin.le, hw]
  rw [heq.fderiv_eq]
  have hmem : endChart p m z ∈ disk := by
    simpa [disk, Metric.mem_ball, dist_zero_right] using hin
  exact (hasFDerivAt_comp_endChart p m z
    (((hu.1 _).contDiffAt (Metric.isOpen_ball.mem_nhds hmem)).differentiableAt
      (by simp)).hasFDerivAt).fderiv

lemma endField_fderiv_outside_energy_general {k m : ℕ} {u : ZMod (2*m) → ℂ → ℂ}
    (hu : IsSmooth k m u) (p : ℂ) (hp : ‖p‖ = 1) (c : ZMod (2*m))
    {z : ℂ} (hz : z ≠ 0) (hr : ‖z‖^m < 1) (hout : 1 < ‖endChart p m z‖) :
    fderiv ℝ (endFieldWith p u (endIdx m c p)) z =
      ((fderiv ℝ (u (endIdx m c p z + 1)) (Bracket.σ (endChart p m z))).comp
        (fderiv ℝ Bracket.σ (endChart p m z))).comp (endDeriv m z) := by
  have hi := endIdx_locally_constant_off_circle p hp c hz hr hout.ne'
  have hEc : ContinuousAt (fun w => ‖endChart p m w‖) z := by
    unfold endChart
    fun_prop
  have heq : endFieldWith p u (endIdx m c p) =ᶠ[𝓝 z]
      (fun w => u (endIdx m c p z + 1) (Bracket.σ (endChart p m w))) := by
    filter_upwards [hi, hEc.eventually (lt_mem_nhds hout)] with w hw hwout
    rw [endFieldWith_outside p u _ hwout, hw]
  rw [heq.fderiv_eq]
  have hmem : Bracket.σ (endChart p m z) ∈ disk := by
    have hn : ‖Bracket.σ (endChart p m z)‖ < 1 := by
      rw [Bracket.norm_σ]
      exact inv_lt_one_of_one_lt₀ hout
    simpa [disk, Metric.mem_ball, dist_zero_right] using hn
  have hu' := ((hu.1 (endIdx m c p z + 1)).contDiffAt (Metric.isOpen_ball.mem_nhds hmem)).differentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hσ := (SigmaDeriv.hasFDerivAt_sigmaR
    (norm_pos_iff.mp (lt_trans zero_lt_one hout))).differentiableAt.hasFDerivAt
  exact ((hu'.hasFDerivAt.comp _ hσ).comp z (hasFDerivAt_endChart p m z)).fderiv

end KsIndex.EndField
