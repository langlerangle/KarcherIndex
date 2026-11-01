module

public import KsIndexLean.KarcherJacobiForward
public import KsIndexLean.EndChartPDE

@[expose] public section


/-! Extending the Jacobi equation to smooth seam germs. -/
noncomputable section
open Set Topology Filter
open scoped ContDiff
namespace KsIndex.KarcherData

/-- Smooth gluing extends the disk equation to a unit-circle point. No equation
is assumed on that circle; continuity of the flat residual proves it. -/
lemma diskJacobi_glue_boundary {k m : ℕ} [NeZero m] (hk : 2 ≤ k)
    {u : ZMod (2*m) → ℂ → ℂ} (hJ : Surface.IsJacobiField k m u)
    (n : ZMod (2*m)) {z : ℂ} (hz : ‖z‖ = 1) (hp : z ∉ Surface.punctures k)
    (hs : ContDiffAt ℝ ∞ (Surface.glue u n) z) :
    diskJacobi k (Surface.glue u n) z = 0 := by
  apply (diskJacobi_eq_zero_iff_flat hk hp _).mpr
  let F : ℂ → ℂ := fun w => Surface.laplacian (Surface.glue u n) w +
    (Surface.potV k w : ℂ) * Surface.glue u n w
  have hc : ContinuousAt F z := by
    have hv : Continuous (fun w => (Surface.potV k w : ℂ)) := by
      apply Complex.continuous_ofReal.comp
      unfold Surface.potV
      exact (continuous_const.mul (continuous_norm.pow _)).div
        (((continuous_norm.pow _).add continuous_const).pow 2) (fun w => by positivity)
    exact (EndChart.continuousAt_laplacian (hs.of_le Surface.two_le_infty)).add
      (hv.continuousAt.mul hs.continuousAt)
  have hzero : ∀ w ∈ Surface.disk, F w = 0 := by
    intro w hw
    have hn : ‖w‖ < 1 := by simpa [Surface.disk, Metric.mem_ball, dist_zero_right] using hw
    have hg := PaperHalfPeriodRealization.glue_interior_germ u n hn
    change Surface.laplacian (Surface.glue u n) w + _ = 0
    rw [JacobiFamily.laplacian_congr hg, hg.eq_of_nhds]
    apply (diskJacobi_eq_zero_iff_flat hk (Surface.punctures_notMem_disk (by omega) hw) _).mp
    simpa only [diskJacobi, Complex.ofReal_pow] using hJ n w hw
  have hcl : z ∈ closure Surface.disk := by
    rw [Surface.disk, closure_ball (0 : ℂ) one_ne_zero, Metric.mem_closedBall, dist_zero_right]
    exact hz.le
  have : (𝓝[Surface.disk] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have ht : Tendsto F (𝓝[Surface.disk] z) (𝓝 (0 : ℂ)) := by
    have he : F =ᶠ[𝓝[Surface.disk] z] fun _ => 0 := by
      filter_upwards [self_mem_nhdsWithin] with w hw using hzero w hw
    exact (tendsto_congr' he).mpr tendsto_const_nhds
  exact tendsto_nhds_unique hc.continuousWithinAt ht

end KsIndex.KarcherData
