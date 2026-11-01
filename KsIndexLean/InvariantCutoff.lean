module

public import KsIndexLean.ReflectionLocalization
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section


open Set Filter Topology Metric
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket

/-- Symmetrize a real cutoff without enlarging its support. -/
def invariantCutoff (ψ : ℂ → ℝ) (z : ℂ) : ℝ := ψ z * ψ (σ z)

lemma invariantCutoff_invariant (ψ : ℂ → ℝ) (z : ℂ) :
    invariantCutoff ψ (σ z) = invariantCutoff ψ z := by
  simp only [invariantCutoff, σ_σ, mul_comm]

lemma invariantCutoff_support (ψ : ℂ → ℝ) :
    tsupport (invariantCutoff ψ) ⊆ tsupport ψ :=
  tsupport_mul_subset_left

lemma invariantCutoff_compact {ψ : ℂ → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport (invariantCutoff ψ) := hc.mul_right

lemma invariantCutoff_smooth {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (h0 : (0 : ℂ) ∉ tsupport ψ) : ContDiff ℝ ∞ (invariantCutoff ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    have he : ψ =ᶠ[𝓝 (0 : ℂ)] 0 := notMem_tsupport_iff_eventuallyEq.mp h0
    have hh : invariantCutoff ψ =ᶠ[𝓝 (0 : ℂ)] 0 := by
      filter_upwards [he] with z hz
      simp [invariantCutoff, hz]
    exact contDiffAt_const.congr_of_eventuallyEq hh
  · exact hψ.contDiffAt.mul (hψ.contDiffAt.comp z (contDiffAt_σ hz))

lemma invariantCutoff_one {ψ : ℂ → ℝ} {p : ℂ} (hp : ‖p‖ = 1)
    (hψ : ψ =ᶠ[𝓝 p] 1) : invariantCutoff ψ =ᶠ[𝓝 p] 1 := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have ht : Tendsto σ (𝓝 p) (𝓝 p) := by
    simpa only [σ_self hp] using (continuousAt_σ hp0).tendsto
  filter_upwards [hψ, ht.eventually hψ] with z hz hi
  simp [invariantCutoff, hz, hi]

/-- A genuine invariant cutoff near a circle point in any prescribed open neighborhood. -/
theorem exists_invariant_cutoff {Ω : Set ℂ} (hΩ : IsOpen Ω) {p : ℂ}
    (hpΩ : p ∈ Ω) (hp : ‖p‖ = 1) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Ω ∧ (0 : ℂ) ∉ tsupport χ ∧
      (∀ z, χ (σ z) = χ z) ∧ χ =ᶠ[𝓝 p] 1 := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have hn : Ω ∩ {0}ᶜ ∈ 𝓝 p :=
    (hΩ.inter isClosed_singleton.isOpen_compl).mem_nhds ⟨hpΩ, hp0⟩
  obtain ⟨r, hr, hsub⟩ := nhds_basis_closedBall.mem_iff.mp hn
  let ψ : ContDiffBump p := ⟨r / 2, r, by positivity, by linarith⟩
  have hs : tsupport (ψ : ℂ → ℝ) ⊆ Ω ∩ {0}ᶜ := by
    rw [ψ.tsupport_eq]
    exact hsub
  have h0 : (0 : ℂ) ∉ tsupport (ψ : ℂ → ℝ) := fun h => (hs h).2 rfl
  refine ⟨invariantCutoff ψ, invariantCutoff_smooth ψ.contDiff h0,
    invariantCutoff_compact ψ.hasCompactSupport, ?_, ?_,
    invariantCutoff_invariant ψ, invariantCutoff_one hp ψ.eventuallyEq_one⟩
  · exact (invariantCutoff_support ψ).trans (hs.trans inter_subset_left)
  · exact fun h => h0 (invariantCutoff_support ψ h)

end KsIndex.Trace
