module

public import KsIndexLean.ClassicalCharacterRepresentative

@[expose] public section


/-! A compact smooth extension preserving the germ on the closed unit disk.
Only smoothness on the radius-two ball is required of the original function. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace

/-- The cutoff is identically one on a neighborhood of the closed unit disk. -/
def closedDiskCutoff : ContDiffBump (0 : ℂ) where
  rIn := 5 / 4
  rOut := 3 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

lemma closedDiskCutoff_support :
    tsupport (closedDiskCutoff : ℂ → ℝ) ⊆ Metric.ball (0 : ℂ) 2 := by
  rw [closedDiskCutoff.tsupport_eq]
  intro z hz
  have h : dist z 0 ≤ 3 / 2 := hz
  exact show dist z 0 < 2 by linarith

/-- The extension retains all derivatives at every point of the closed disk. -/
theorem exists_global_smooth_disk_extension {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Metric.ball 0 2)) :
    ∃ G : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧ HasCompactSupport G ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, G =ᶠ[nhds z] f := by
  let G (z : ℂ) := closedDiskCutoff z • f z
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ Metric.ball (0 : ℂ) 2
    · exact closedDiskCutoff.contDiff.contDiffAt.smul
        (hf.contDiffAt (Metric.isOpen_ball.mem_nhds hz))
    · have hn : z ∉ tsupport (closedDiskCutoff : ℂ → ℝ) :=
        fun h => hz (closedDiskCutoff_support h)
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with w hw
      simp only [G, hw, Pi.zero_apply, zero_smul]
  refine ⟨G, hG, closedDiskCutoff.hasCompactSupport.smul_right, ?_⟩
  intro z hz
  have hz' : z ∈ Metric.ball (0 : ℂ) (5 / 4) := by
    have h : dist z 0 ≤ 1 := hz
    exact show dist z 0 < 5 / 4 by linarith
  apply Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hz')
  intro w hw
  have hc : closedDiskCutoff w = 1 := closedDiskCutoff.one_of_mem_closedBall
    (show dist w 0 ≤ 5 / 4 from le_of_lt hw)
  simp only [G, hc, one_smul]

end KsIndex.Trace
