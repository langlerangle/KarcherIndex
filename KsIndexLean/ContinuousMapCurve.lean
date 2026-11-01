module

public import KsIndexLean.BanachIntervalFTC
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A continuous family of pointwise derivatives gives differentiation in the sup norm. -/
theorem continuousMap_hasDerivAt_of_pointwise {f g : ℝ → C(X, E)} (hg : Continuous g)
    (hd : ∀ t x, HasDerivAt (fun r => f r x) (g t x) t) (t : ℝ) :
    HasDerivAt f (g t) t := by
  have he : f = fun r => f 0 + ∫ s in 0..r, g s := by
    funext r
    ext x
    change f r x = f 0 x + (ContinuousMap.evalCLM ℝ x) (∫ s in 0..r, g s)
    rw [← (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm
      (hg.intervalIntegrable 0 r)]
    change f r x = f 0 x + ∫ s in 0..r, g s x
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s x)
      (((ContinuousMap.evalCLM ℝ x).continuous.comp hg).intervalIntegrable 0 r)]
    abel
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).const_add (f 0)

end KsIndex.Trace
