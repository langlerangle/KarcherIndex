module

public import KsIndexLean.LocalTrace
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace

/-- A local continuous extension can be replaced by a global one on a smaller ball. -/
lemma exists_global_continuous_local {O : Set ℂ} (hO : IsOpen O) {f : ℂ → ℂ}
    (hf : ContinuousOn f O) {x : ℂ} (hx : x ∈ O) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ g : ℂ → ℂ, Continuous g ∧ EqOn g f (Metric.ball x ε) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hx)
  let ψ : ContDiffBump x :=
    { rIn := δ / 4
      rOut := δ / 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  let g : ℂ → ℂ := fun z => ψ z • f z
  have hs : tsupport g ⊆ O := by
    apply (tsupport_smul_subset_left (fun z => ψ z) f).trans
    rw [ψ.tsupport_eq]
    intro z hz
    apply hball
    change dist z x < δ
    have hz' : dist z x ≤ δ / 2 := Metric.mem_closedBall.mp hz
    linarith
  refine ⟨δ / 4, by linarith, g, ?_, ?_⟩
  · exact (ψ.continuous.continuousOn.smul hf).continuous_of_tsupport_subset hO hs
  · intro z hz
    change ψ z • f z = f z
    rw [ψ.one_of_mem_closedBall (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hz).le),
      one_smul]

end KsIndex.Trace
