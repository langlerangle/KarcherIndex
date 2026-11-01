module

public import KsIndexLean.HemisphereFiniteExtension
public import KsIndexLean.JacobiWeakTrace

@[expose] public section


noncomputable section
open Set Filter Topology Metric
open scoped ContDiff
namespace KsIndex.Spherical
open MeasureTheory KsIndex.WeakH1 KsIndex.Trace
lemma hemisphere_germs_chart_smooth (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p) :
    ContDiffOn ℝ ∞ (f ∘ sphereChart) (WeakH1.disk : Set ℂ) := by
  intro z hz
  have hz' : ‖z‖ ≤ 1 := le_of_lt (by simpa [WeakH1.disk, mem_ball, dist_zero_right] using hz)
  obtain ⟨F, hF, he⟩ := hf (sphereChart z) (sphereChart_closed_lower hz')
  have heq : (f ∘ sphereChart) =ᶠ[𝓝 z] (F ∘ stereoPoint) := by
    have hpull := continuous_sphereChart.continuousAt.tendsto.eventually he
    filter_upwards [hpull, WeakH1.disk.isOpen.mem_nhds hz] with w hw hwb
    exact hw (sphereChart_closed_lower (le_of_lt (by
      simpa [WeakH1.disk, mem_ball, dist_zero_right] using hwb)))
  exact ((hF.comp z contDiff_stereoPoint.contDiffAt).congr_of_eventuallyEq heq).contDiffWithinAt

lemma chart_memLp_jet_of_C1_extension (f G : ℂ → ℂ) (hG : ContDiff ℝ 1 G)
    (he : ∀ z ∈ (WeakH1.disk : Set ℂ), f z = G z) :
    MemLp f 2 (volume.restrict (WeakH1.disk : Set ℂ)) ∧
    MemLp (fun z => fderiv ℝ f z 1) 2 (volume.restrict (WeakH1.disk : Set ℂ)) ∧
    MemLp (fun z => fderiv ℝ f z Complex.I) 2 (volume.restrict (WeakH1.disk : Set ℂ)) := by
  have hd : ∀ z ∈ WeakH1.disk, fderiv ℝ f z = fderiv ℝ G z := by
    intro z hz
    exact Filter.EventuallyEq.fderiv_eq
      (Filter.Eventually.mono (WeakH1.disk.isOpen.mem_nhds hz) (fun y hy => he y hy))
  have hv : f =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] G := by
    filter_upwards [ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with z hz
    exact he z hz
  have hdir (v : ℂ) : (fun z => fderiv ℝ f z v)
      =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] (fun z => fderiv ℝ G z v) := by
    filter_upwards [ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with z hz
    rw [hd z hz]
  have hc : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  exact ⟨(continuous_memLp_disk hG.continuous).ae_eq hv.symm,
    (continuous_memLp_disk (hc.clm_apply continuous_const)).ae_eq (hdir 1).symm,
    (continuous_memLp_disk (hc.clm_apply continuous_const)).ae_eq (hdir Complex.I).symm⟩

lemma hemisphere_germs_chart_memLp (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p) :
    MemLp (f ∘ sphereChart) 2 (volume.restrict (WeakH1.disk : Set ℂ)) ∧
    MemLp (fun z => fderiv ℝ (f ∘ sphereChart) z 1) 2 (volume.restrict (WeakH1.disk : Set ℂ)) ∧
    MemLp (fun z => fderiv ℝ (f ∘ sphereChart) z Complex.I) 2
      (volume.restrict (WeakH1.disk : Set ℂ)) := by
  obtain ⟨G, hG, _, he⟩ := hemisphere_germs_finite_chart_extension f hf 1
  exact chart_memLp_jet_of_C1_extension (f ∘ sphereChart) G hG he

/-- Disk Sobolev data for a function smooth in ambient germs up to the equator. -/
def hemisphereGermData (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p) : SmoothH1Data where
  F := f ∘ sphereChart
  smooth := hemisphere_germs_chart_smooth f hf
  value_mem := (hemisphere_germs_chart_memLp f hf).1
  dx_mem := (hemisphere_germs_chart_memLp f hf).2.1
  dy_mem := (hemisphere_germs_chart_memLp f hf).2.2

/-- The weak disk carrier retains the actual spherical function in coordinates. -/
def hemisphereGermH1 (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p) : ComplexH1 :=
  smoothToH1 (hemisphereGermData f hf)

/-- Its trace is the actual equatorial boundary value almost everywhere. -/
lemma hemisphereGermH1_trace (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p) :
    (diskTraceCLM (hemisphereGermH1 f hf) : Circle₁ → ℂ) =ᵐ[circleMeasure]
      (fun w => f (sphereChart w)) :=
by
  obtain ⟨G, hG, _, he⟩ := hemisphere_germs_finite_closed_chart_extension f hf 1
  have hv : valueCLM (hemisphereGermH1 f hf) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] G := by
    filter_upwards [smoothToH1_value_ae (hemisphereGermData f hf),
      ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with z hz hzd
    exact hz.trans (he z (ball_subset_closedBall hzd))
  have ht := diskTrace_coe_ae hG.continuous.continuousOn hv
  filter_upwards [ht] with w hw
  exact hw.trans (he w (by
    have hn : ‖(w : ℂ)‖ = 1 := by
      simpa only [Circle₁, mem_sphere, dist_zero_right] using w.property
    simp [mem_closedBall, dist_zero_right, hn])).symm
lemma hemisphereGermH1_value (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p) :
    valueCLM (hemisphereGermH1 f hf) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)]
      (f ∘ sphereChart) := smoothToH1_value_ae _

lemma hemisphereGermH1_dx (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p) :
    dxCLM (hemisphereGermH1 f hf) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)]
      (fun z => fderiv ℝ (f ∘ sphereChart) z 1) := smoothToH1_dx_ae _

lemma hemisphereGermH1_dy (f : Sphere → ℂ)
    (hf : ∀ p : Sphere, p.val 2 ≤ 0 → HasSmoothClosedHemisphereGerm f p) :
    dyCLM (hemisphereGermH1 f hf) =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)]
      (fun z => fderiv ℝ (f ∘ sphereChart) z Complex.I) := smoothToH1_dy_ae _
end KsIndex.Spherical
