module

public import KsIndexLean.OperatorL2Continuity
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace

lemma lipschitz_comp_toLp {μ : Measure ℂ} {F : ℂ → ℂ} {C : NNReal}
    (hF : LipschitzWith C F) (h0 : F 0 = 0) {u : ℂ → ℂ} (hu : MemLp u 2 μ) :
    hF.compLp h0 (hu.toLp u) = (hF.comp_memLp h0 hu).toLp (F ∘ u) := by
  apply Lp.ext
  filter_upwards [hF.coeFn_compLp h0 (hu.toLp u), hu.coeFn_toLp,
    (hF.comp_memLp h0 hu).coeFn_toLp] with z hz hu hv
  simpa only [Function.comp_apply, hu, hv] using hz

lemma lipschitz_toLp_tendsto {μ : Measure ℂ} {F : ℂ → ℂ} {C : NNReal}
    (hF : LipschitzWith C F) (h0 : F 0 = 0) {u : ℕ → ℂ → ℂ} {v : ℂ → ℂ}
    (hu : ∀ n, MemLp (u n) 2 μ) (hv : MemLp v 2 μ)
    (ht : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hv.toLp v))) :
    Tendsto (fun n => (hF.comp_memLp h0 (hu n)).toLp (F ∘ u n)) atTop
      (𝓝 ((hF.comp_memLp h0 hv).toLp (F ∘ v))) := by
  have h := ((hF.continuous_compLp h0).tendsto (hv.toLp v)).comp ht
  have he : (fun n => hF.compLp h0 ((hu n).toLp (u n))) =
      (fun n => (hF.comp_memLp h0 (hu n)).toLp (F ∘ u n)) := by
    funext n
    exact lipschitz_comp_toLp hF h0 (hu n)
  change Tendsto (fun n => hF.compLp h0 ((hu n).toLp (u n))) atTop
    (𝓝 (hF.compLp h0 (hv.toLp v))) at h
  rw [he, lipschitz_comp_toLp hF h0 hv] at h
  exact h

lemma hasLineDerivAt_nonlinear_comp {F u : ℂ → ℂ} {D : ℂ →L[ℝ] ℂ} {v z d : ℂ}
    (hF : HasFDerivAt F D (u z)) (hu : HasLineDerivAt ℝ u v z d) :
    HasLineDerivAt ℝ (F ∘ u) (D v) z d := by
  have hF' : HasFDerivAt F D (u (z + (0 : ℝ) • d)) := by
    simpa only [zero_smul, add_zero] using hF
  exact hF'.comp_hasDerivAt 0 hu

end KsIndex.Trace
