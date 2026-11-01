module

public import KsIndexLean.PhaseAverageL2
public import KsIndexLean.SmoothReflectionProjection

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket

lemma reflectionAverage_eq_phaseAverage (s : ℂ) (u : ℂ → ℂ) :
    reflectionAverage s u = phaseAverage s u (u ∘ σ) := by
  funext z
  rw [phaseAverage_apply]
  rfl

lemma reflectionAverage_memLp (s : ℂ) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2))) :
    MemLp (reflectionAverage s u) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) := by
  rw [reflectionAverage_eq_phaseAverage]
  exact phaseAverage_memLp s hu (memLp_sigma_collar hu)

lemma reflectionAverage_tendsto (s : ℂ) {u : ℕ → ℂ → ℂ} {v : ℂ → ℂ}
    (hu : ∀ n, MemLp (u n) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hv : MemLp v 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (ht : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hv.toLp v))) :
    Tendsto (fun n => (reflectionAverage_memLp s (hu n)).toLp (reflectionAverage s (u n)))
      atTop (𝓝 ((reflectionAverage_memLp s hv).toLp (reflectionAverage s v))) := by
  simp only [reflectionAverage_eq_phaseAverage]
  exact phaseAverage_tendsto s hu (fun n => memLp_sigma_collar (hu n))
    hv (memLp_sigma_collar hv) ht (toLp_sigma_collar_tendsto hu hv ht)

end KsIndex.Trace
