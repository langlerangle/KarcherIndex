module

public import KsIndexLean.UnweightedL2Supply
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public section


/-!
The annular anchor requires no bound at the puncture: continuity on one
compact annulus suffices. The energy premise below remains explicit.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace KsIndex.EndChart

lemma isCompact_dyadicAnnulus (R : ℝ) : IsCompact (dyadicAnnulus R) := by
  apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro z hz
    simpa [Metric.mem_closedBall, dist_zero_right] using hz.2

lemma memLp_on_dyadicAnnulus_of_continuousOn
    {F : Type*} [NormedAddCommGroup F] {v : ℂ → F} {R : ℝ}
    (hv : ContinuousOn v (dyadicAnnulus R)) :
    MemLp v 2 (volume.restrict (dyadicAnnulus R)) := by
  have hK := isCompact_dyadicAnnulus R
  let : IsFiniteMeasure (volume.restrict (dyadicAnnulus R)) :=
    ⟨by simpa using hK.measure_lt_top (μ := volume)⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hv
  apply MemLp.of_bound (hv.aestronglyMeasurable hK.measurableSet) C
  exact (ae_restrict_mem hK.measurableSet).mono hC

/-- A C² field on a larger punctured ball has unweighted L² on every smaller
punctured closed disk on which its derivative has finite energy. -/
theorem memLp_two_of_contDiffAt_energy
    {R r₀ : ℝ} (hR : 0 < R) (hRr : R < r₀) (v : ℂ → ℝ)
    (hsm : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r₀ → ContDiffAt ℝ 2 v z)
    (hE : (∫⁻ z in puncturedDisk R, ‖fderiv ℝ v z‖ₑ ^ 2 ∂volume) ≠ ⊤) :
    MemLp v 2 (volume.restrict (puncturedDisk R)) := by
  have hs : ∀ z ∈ puncturedDisk R, ContDiffAt ℝ 2 v z :=
    fun z hz => hsm z hz.1 (lt_of_le_of_lt hz.2 hRr)
  apply memLp_two_of_energy_anchor hR v (fderiv ℝ v)
  · intro z hz
    exact ((hs z hz).differentiableAt (by norm_num)).hasFDerivAt
  · intro z hz
    exact ((hs z hz).continuousAt_fderiv (by norm_num)).continuousWithinAt
  · exact hE
  · apply (memLp_on_dyadicAnnulus_of_continuousOn ?_).eLpNorm_lt_top.ne
    intro z hz
    exact (hsm z (lt_of_lt_of_le (by linarith : 0 < R / 2) hz.1)
      (lt_of_le_of_lt hz.2 hRr)).continuousAt.continuousWithinAt

/-- Restoring the center costs no integrability: its volume is zero. -/
theorem memLp_ball_of_memLp_puncturedDisk
    {F : Type*} [NormedAddCommGroup F] {v : ℂ → F} {R : ℝ}
    (hv : MemLp v 2 (volume.restrict (puncturedDisk R))) :
    MemLp v 2 (volume.restrict (Metric.ball (0 : ℂ) R)) := by
  have hsub : Metric.ball (0 : ℂ) R \ {0} ⊆ puncturedDisk R := by
    intro z hz
    refine ⟨norm_pos_iff.mpr ?_, ?_⟩
    · simpa using hz.2
    · exact (by simpa [Metric.mem_ball, dist_zero_right] using hz.1 :
        ‖z‖ < R).le
  have hm := hv.mono_measure (Measure.restrict_mono hsub le_rfl)
  have heq : Metric.ball (0 : ℂ) R \ {0} =ᵐ[volume] Metric.ball (0 : ℂ) R := by
    filter_upwards [show ∀ᵐ z : ℂ ∂volume, z ≠ 0 from
      by simp [ae_iff]] with z hz
    simp [hz]
  rwa [Measure.restrict_congr_set heq] at hm

end KsIndex.EndChart
