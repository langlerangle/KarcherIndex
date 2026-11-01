module

public import KsIndexLean.CutoffDiskReconstruction
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

@[expose] public section


open Set MeasureTheory TopologicalSpace
open scoped ContDiff Topology

noncomputable section
namespace KsIndex.Trace

/-- Every point of an open circle arc has a smooth ambient cutoff equal to one
near that point and vanishing at circle points outside the arc. -/
theorem exists_seam_cutoff {A : Set Circle₁} (hA : IsOpen A) {w : Circle₁} (hw : w ∈ A) :
    ∃ η : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧
      (∀ x : Circle₁, x ∉ A → η x = 0) ∧ η =ᶠ[𝓝 (w : ℂ)] (fun _ => 1) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hA w hw
  let f : ContDiffBump (w : ℂ) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  refine ⟨f, f.contDiff, ?_, f.eventuallyEq_one⟩
  intro x hx
  apply f.zero_of_le_dist
  by_contra hd
  have hd' : dist (x : ℂ) (w : ℂ) < ε / 2 := lt_of_not_ge hd
  have hxball : x ∈ Metric.ball w ε := by
    change dist (x : ℂ) (w : ℂ) < ε
    linarith
  exact hx (hball hxball)

lemma angularTestDeriv_eventually_zero {η : ℂ → ℝ} {w : ℂ}
    (h : η =ᶠ[𝓝 w] (fun _ => 1)) : angularTestDeriv η =ᶠ[𝓝 w] (fun _ => 0) := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with z hz
  simp only [angularTestDeriv, hz, fderiv_const_apply, zero_apply]

lemma continuousAt_nUnit_circle (w : Circle₁) : ContinuousAt nUnit (w : ℂ) := by
  have hz : (w : ℂ) ≠ 0 := by
    intro h
    have hn : ‖(w : ℂ)‖ = 1 := by simp
    rw [h, norm_zero] at hn
    norm_num at hn
  exact (hasFDerivAt_nUnit hz).continuousAt

lemma nUnit_circle (w : Circle₁) : nUnit (w : ℂ) = (w : ℂ) := by
  simpa using nUnit_of_circle 1 zero_lt_one w

/-- Both the cutoff and its angular derivative become constant near a seam point. -/
lemma cutoff_coefficients_near_circle {η : ℂ → ℝ} {w : Circle₁}
    (h : η =ᶠ[𝓝 (w : ℂ)] (fun _ => 1)) :
    ∀ᶠ z in 𝓝 (w : ℂ), η (nUnit z) = 1 ∧ angularTestDeriv η (nUnit z) = 0 := by
  have ht : Filter.Tendsto nUnit (𝓝 (w : ℂ)) (𝓝 (w : ℂ)) := by
    simpa only [ContinuousAt, nUnit_circle] using (continuousAt_nUnit_circle w)
  exact ht.eventually (h.and (angularTestDeriv_eventually_zero h))

end KsIndex.Trace
