module

public import KsIndexLean.LocalizedMollification
public import KsIndexLean.SmoothReflectionProjection

@[expose] public section


open Set Filter Topology MeasureTheory Metric ContinuousLinearMap
open scoped Convolution ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket

/-- An AE zero neighborhood becomes a pointwise zero neighborhood after small convolution. -/
lemma compactMollify_zero_of_ae_ball (φ : ContDiffBump (0 : ℂ))
    {u : ℂ → ℂ} {p z : ℂ} {R : ℝ}
    (hu : ∀ᵐ w ∂volume, dist w p < R → u w = 0)
    (hz : dist z p + φ.rOut ≤ R) : compactMollify φ u z = 0 := by
  have he := (quasiMeasurePreserving_sub_left_of_right_invariant volume z).tendsto_ae.eventually hu
  rw [compactMollify, convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards [he] with t ht
  by_cases hk : φ.normed volume t = 0
  · simp [hk]
  · have ht0 : dist t 0 < φ.rOut := by
      have hm : t ∈ Function.support (φ.normed volume) := hk
      rw [φ.support_normed_eq] at hm
      exact hm
    have hd : dist (z - t) p ≤ dist z p + dist t 0 := by
      calc
        dist (z - t) p ≤ dist (z - t) z + dist z p := dist_triangle _ _ _
        _ = dist z p + dist t 0 := by simp [dist_eq_norm, add_comm]
    have hh : u (z - t) = 0 := ht (by linarith)
    simp [hh]

lemma shrinkingMollifier_zero_ball {u : ℂ → ℂ} {p : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : ∀ᵐ w ∂volume, dist w p < R → u w = 0) :
    ∀ᶠ n in atTop, ∀ z, dist z p < R / 2 →
      compactMollify (shrinkingMollifier n) u z = 0 := by
  have hr := shrinkingMollifier_radius.eventually (gt_mem_nhds (half_pos hR))
  filter_upwards [hr] with n hn
  intro z hz
  exact compactMollify_zero_of_ae_ball _ hu (by linarith)

/-- Reflection averaging retains a fixed smaller hole near every circle puncture. -/
theorem reflected_mollifier_zero_ball (s : ℂ) {u : ℂ → ℂ} {p : ℂ}
    (hp : ‖p‖ = 1) {R : ℝ} (hR : 0 < R)
    (hu : ∀ᵐ w ∂volume, dist w p < R → u w = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ z, dist z p < δ →
      reflectionAverage s (compactMollify (shrinkingMollifier n) u) z = 0 := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have ht : Tendsto σ (𝓝 p) (𝓝 p) := by
    simpa only [σ_self hp] using (continuousAt_σ hp0).tendsto
  have hb : ball p (R / 2) ∈ 𝓝 p := ball_mem_nhds p (half_pos hR)
  have hi : σ ⁻¹' ball p (R / 2) ∈ 𝓝 p := ht hb
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hb hi)
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [shrinkingMollifier_zero_ball hR hu] with n hn
  intro z hz
  have hh := hsub hz
  simp [reflectionAverage, hn z hh.1, hn (σ z) hh.2]

end KsIndex.Trace
