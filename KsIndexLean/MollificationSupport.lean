module

public import KsIndexLean.LocalizedMollification
public import KsIndexLean.SmoothReflectionProjection
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section


open Set Filter Topology MeasureTheory Metric ContinuousLinearMap
open scoped Convolution Pointwise
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket

lemma compactMollify_tsupport_subset (φ : ContDiffBump (0 : ℂ)) (u : ℂ → ℂ) :
    tsupport (compactMollify φ u) ⊆ cthickening φ.rOut (tsupport u) := by
  apply closure_minimal _ isClosed_cthickening
  intro z hz
  have hm := support_convolution_subset (lsmul ℝ ℝ) hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hm
  rw [φ.support_normed_eq] at ha
  have haNorm : ‖a‖ < φ.rOut := by simpa only [mem_ball, dist_zero_right] using ha
  apply mem_cthickening_of_dist_le (a + b) b φ.rOut (tsupport u)
    (subset_closure hb)
  simpa only [dist_eq_norm, add_sub_cancel_right, sub_zero] using haNorm.le

/-- Compactly supported inputs remain in any prescribed open neighborhood at small scales. -/
theorem mollifier_support_open {u : ℂ → ℂ} (hc : HasCompactSupport u)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hs : tsupport u ⊆ Ω) :
    ∀ᶠ n in atTop, tsupport (compactMollify (shrinkingMollifier n) u) ⊆ Ω := by
  obtain ⟨r, hr, hsub⟩ := hc.exists_cthickening_subset_open hΩ hs
  filter_upwards [shrinkingMollifier_radius.eventually (gt_mem_nhds hr)] with n hn
  exact (compactMollify_tsupport_subset _ _).trans
    ((cthickening_mono hn.le _).trans hsub)

/-- Inversion of a compact support away from zero is compact. -/
lemma sigma_tsupport_compact {f : ℂ → ℂ} (hc : HasCompactSupport f)
    (h0 : (0 : ℂ) ∉ tsupport f) : IsCompact (σ '' tsupport f) := by
  apply hc.image_of_continuousOn
  intro z hz
  exact (continuousAt_σ (fun h => h0 (h ▸ hz))).continuousWithinAt

lemma reflectionAverage_tsupport (s : ℂ) {f : ℂ → ℂ} (hc : HasCompactSupport f)
    (h0 : (0 : ℂ) ∉ tsupport f) :
    tsupport (reflectionAverage s f) ⊆ tsupport f ∪ σ '' tsupport f := by
  apply closure_minimal _ (isClosed_closure.union (sigma_tsupport_compact hc h0).isClosed)
  intro z hz
  by_contra hn
  have h1 : z ∉ tsupport f := fun h => hn (Or.inl h)
  have h2 : σ z ∉ tsupport f := by
    intro h
    exact hn (Or.inr ⟨σ z, h, σ_σ z⟩)
  apply hz
  simp [reflectionAverage, image_eq_zero_of_notMem_tsupport h1,
    image_eq_zero_of_notMem_tsupport h2]

/-- Local reflected smoothing cannot leak out of an invariant open neighborhood. -/
theorem reflected_mollifier_support_open (s : ℂ) {u : ℂ → ℂ}
    (hc : HasCompactSupport u) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hs : tsupport u ⊆ Ω) (h0 : (0 : ℂ) ∉ Ω) (hi : MapsTo σ Ω Ω) :
    ∀ᶠ n in atTop,
      tsupport (reflectionAverage s (compactMollify (shrinkingMollifier n) u)) ⊆ Ω := by
  filter_upwards [mollifier_support_open hc hΩ hs] with n hn
  have hz : (0 : ℂ) ∉ tsupport (compactMollify (shrinkingMollifier n) u) :=
    fun h => h0 (hn h)
  apply (reflectionAverage_tsupport s (compactMollify_support _ hc) hz).trans
  rintro z (hz | ⟨w, hw, rfl⟩)
  · exact hn hz
  · exact hi (hn hw)

end KsIndex.Trace
