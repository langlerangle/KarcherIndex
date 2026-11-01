module

public import KsIndexLean.NaturalCoreH1

@[expose] public section


/-! Finiteness of both conformal Jacobi densities on natural compact tests. -/
noncomputable section
open Set MeasureTheory
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.SingleDisk
namespace KsIndex.Trace

lemma natCc_integrable_gradSq {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool} {f : ℂ → ℂ}
    (hf : f ∈ NatCc k b1 b0) : IntegrableOn (gradSq f) Surface.disk := by
  obtain ⟨hv,hx,hy⟩ := natCc_memLp_jet hk hf
  exact ((memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mp hx).add
    ((memLp_two_iff_integrable_sq_norm hy.aestronglyMeasurable).mp hy)

lemma natCc_integrable_potential {k : ℕ} (hk : 1 ≤ k) {b1 b0 : Bool} {f : ℂ → ℂ}
    (hf : f ∈ NatCc k b1 b0) :
    IntegrableOn (fun z => potV k z * ‖f z‖^2) Surface.disk := by
  obtain ⟨G,hG,he⟩ := SeamUpper.natCc_extension hk hf
  have hi : IntegrableOn (fun z => potV k z * ‖G z‖^2) (Metric.closedBall (0 : ℂ) 1) := ((continuous_potV k).mul (hG.continuous.norm.pow 2)).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : ℂ) 1)
  apply (hi.mono_set Metric.ball_subset_closedBall).congr_fun _ measurableSet_ball
  intro z hz
  dsimp only
  rw [he z hz]

lemma natCc_integrable_conformal_densities {k : ℕ} (hk : 2 ≤ k)
    {b1 b0 : Bool} {f : ℂ → ℂ} (hf : f ∈ NatCc k b1 b0) :
    IntegrableOn (fun z => (gradSq f z / rho k z^2) * rho k z^2) Surface.disk ∧
    IntegrableOn (fun z => (absA k z * ‖f z‖)^2 * rho k z^2) Surface.disk := by
  have hk1 : 1 ≤ k := by omega
  constructor
  · apply (natCc_integrable_gradSq hk1 hf).congr_fun _ measurableSet_ball
    intro z hz
    exact (dirichlet_integrand hk1 f (punctures_notMem_disk hk1 hz)).symm
  · apply (natCc_integrable_potential hk1 hf).congr_fun _ measurableSet_ball
    intro z hz
    exact (potential_integrand hk f (punctures_notMem_disk hk1 hz)).symm

end KsIndex.Trace
