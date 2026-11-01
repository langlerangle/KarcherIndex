module

public import KsIndexLean.Caccioppoli

@[expose] public section


/-! Classical bounded Jacobi fields on a punctured closed half-period disk.
The boundary hypotheses are one-sided smoothness and the actual Dirichlet
value or Neumann normal condition; reflected smoothness and H1 membership
are deliberately not assumed. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Trace
open KsIndex.Surface KsIndex.SurfaceForm KsIndex.JacobiFields KsIndex.FaithfulInjection

/-- Coordinate data for a bounded classical half-period field. Values at deleted
punctures and outside the closed disk carry no conditions. -/
structure ClassicalHalfDiskJacobi (k : ℕ) (neumann : Bool) where
  value : ℂ → ℂ
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) value (disk : Set ℂ)
  bounded : ∃ C : ℝ, ∀ w : ℂ, ‖w‖ ≤ 1 → w ∉ punctures k → ‖value w‖ ≤ C
  equation : ∀ w ∈ (disk : Set ℂ), laplacian value w + (potV k w : ℂ) * value w = 0
  boundary : ∀ w : ℂ, ‖w‖ = 1 → w ∉ punctures k →
    ∃ F : ℂ → ℂ, ContDiffAt ℝ (⊤ : ℕ∞) F w ∧
      (∀ᶠ z in nhds w, ‖z‖ ≤ 1 → value z = F z) ∧
      if neumann then fderiv ℝ F w w = 0 else F w = 0

namespace ClassicalHalfDiskJacobi
variable {k : ℕ} {b : Bool} (u : ClassicalHalfDiskJacobi k b)

/-- Interior and boundary germs supply exactly the local input to the cutoff estimate. -/
lemma disk_germ {w : ℂ} (hw : ‖w‖ ≤ 1) (hp : w ∉ punctures k) :
    ∃ F : ℂ → ℂ, ContDiffAt ℝ (⊤ : ℕ∞) F w ∧ u.value =ᶠ[nhdsWithin w disk] F := by
  rcases lt_or_eq_of_le hw with hi | he
  · have hd : w ∈ disk := Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hi)
    exact ⟨u.value, u.smooth.contDiffAt (Metric.isOpen_ball.mem_nhds hd), Filter.EventuallyEq.rfl⟩
  · obtain ⟨F, hF, hs, _⟩ := u.boundary w he hp
    refine ⟨F, hF, ?_⟩
    filter_upwards [hs.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hd
    exact hz (le_of_lt (by simpa only [dist_zero_right] using Metric.mem_ball.mp hd))

/-- Puncture-cutoff energies are finite without assuming a reflected field. -/
theorem cutoff_energy_integrable (hk : 2 ≤ k) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    IntegrableOn (fun w => (PunctureCutoff.cutP k ε w) ^ 2 * gradSq u.value w) disk :=
  integrableOn_cutPSq_gradSq_of_disk_germs hk (fun _ hw hp => u.disk_germ hw hp) h0 h1

/-- Boundedness supplies the value-L2 input, independently of derivative energy. -/
theorem value_sq_integrable (hk : 1 ≤ k) :
    IntegrableOn (fun w => ‖u.value w‖ ^ 2) disk := by
  obtain ⟨C, hC⟩ := u.bounded
  have hc : IntegrableOn (fun _ : ℂ => C ^ 2) disk := integrableOn_const measure_ball_lt_top.ne
  refine hc.mono' ((u.smooth.continuousOn.norm.pow 2).aestronglyMeasurable measurableSet_disk) ?_
  apply ae_restrict_of_forall_mem measurableSet_disk
  intro w hw
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hn : ‖w‖ ≤ 1 := (mem_disk_iff.mp hw).le
  exact pow_le_pow_left₀ (norm_nonneg _) (hC w hn (punctures_notMem_disk hk hw)) 2

end ClassicalHalfDiskJacobi
end KsIndex.Trace
