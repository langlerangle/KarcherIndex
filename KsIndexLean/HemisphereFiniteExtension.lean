module

public import KsIndexLean.HemisphereIntrinsicSmooth
public import KsIndexLean.ClosedDiskExt

@[expose] public section

noncomputable section
open Set Filter Topology Metric
open scoped ContDiff
namespace KsIndex.Spherical
lemma sphereChart_closed_lower {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (sphereChart z).val 2 ≤ 0 := by
  change (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2) ≤ 0
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [norm_nonneg z]
  · positivity

/-- Local smooth ambient germs on the closed lower hemisphere give, for each
finite order, a compactly supported chart extension agreeing on the open disk.
No single globally infinitely smooth extension is asserted. -/
theorem hemisphere_germs_finite_chart_extension (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p) (m : ℕ) :
    ∃ G : ℂ → ℂ, ContDiff ℝ m G ∧ HasCompactSupport G ∧
      ∀ z ∈ ball (0 : ℂ) 1, f (sphereChart z) = G z := by
  apply KsIndex.ClosedDiskExt.exists_finite_order_extension (f ∘ sphereChart) _ m
  intro z hz
  have hz' : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hz
  obtain ⟨F, hF, he⟩ := hf (sphereChart z) (sphereChart_closed_lower hz')
  refine ⟨F ∘ stereoPoint, hF.comp z contDiff_stereoPoint.contDiffAt, ?_⟩
  have hpull := continuous_sphereChart.continuousAt.tendsto.eventually he
  filter_upwards [hpull] with w hw hwb
  have hwn : ‖w‖ ≤ 1 := le_of_lt (by simpa [mem_ball, dist_zero_right] using hwb)
  exact hw (sphereChart_closed_lower hwn)
/-- Ambient smooth germs give continuity on the full closed coordinate disk. -/
lemma hemisphere_germs_chart_continuousOn (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p) :
    ContinuousOn (f ∘ sphereChart) (closedBall (0 : ℂ) 1) := by
  intro z hz
  have hz' : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hz
  obtain ⟨F, hF, he⟩ := hf (sphereChart z) (sphereChart_closed_lower hz')
  have hc : ContinuousWithinAt (F ∘ stereoPoint) (closedBall (0 : ℂ) 1) z :=
    (hF.comp z contDiff_stereoPoint.contDiffAt).continuousAt.continuousWithinAt
  apply hc.congr_of_eventuallyEq_of_mem _ hz
  have hpull := continuous_sphereChart.continuousAt.tendsto.eventually he
  filter_upwards [hpull.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hwb
  exact hw (sphereChart_closed_lower (by simpa [mem_closedBall, dist_zero_right] using hwb))

/-- The finite-order extension agrees also on the boundary, by continuity
and density of the open disk in the closed disk. -/
theorem hemisphere_germs_finite_closed_chart_extension (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p) (m : ℕ) :
    ∃ G : ℂ → ℂ, ContDiff ℝ m G ∧ HasCompactSupport G ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, f (sphereChart z) = G z := by
  obtain ⟨G, hG, hc, he⟩ := hemisphere_germs_finite_chart_extension f hf m
  refine ⟨G, hG, hc, ?_⟩
  have hcl : closure (ball (0 : ℂ) 1) = closedBall (0 : ℂ) 1 := closure_ball _ (by norm_num)
  exact Set.EqOn.of_subset_closure he
    (hemisphere_germs_chart_continuousOn f hf) hG.continuous.continuousOn
    ball_subset_closedBall (by rw [hcl])
end KsIndex.Spherical
