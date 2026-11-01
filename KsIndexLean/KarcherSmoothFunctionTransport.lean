module

public import KsIndexLean.KarcherSeamBoundarySmooth
public import KsIndexLean.KarcherCompactSupportConverse

@[expose] public section


/-! The paper's canonical smooth disk families are precisely smooth functions
on the actual EW period quotient. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open scoped ParameterAtlas
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

lemma contMDiff_iff_isSmooth_encoding (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f ↔
      Surface.IsSmooth k m (encodeDiskFunction (R.diskFunctionPullback f)) := by
  letI := HeightLift.periodChartedSpace R.hC m
  constructor
  · intro hf
    refine ⟨?_, ?_, encodeDiskFunction_exterior _⟩
    · intro n z hz
      have hn : ‖z‖ < 1 := by simpa [Surface.disk, Metric.mem_ball, dist_zero_right] using hz
      let w : PuncturedClosedDisk k := ⟨⟨z, Surface.punctures_notMem_disk (by have hk := h.out; omega) hz⟩, hn.le⟩
      obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n
      · have hj : ((j.val : ℤ) : ZMod m) = j := by simp
        have hs := (R.contMDiffAt_evenPeriodPoint_iff f (j.val : ℤ) w hn).mp (hf _)
        simpa only [hj] using hs.contDiffWithinAt (s := Surface.disk)
      · have hj : ((j.val : ℤ) : ZMod m) = j := by simp
        have hs := (R.contMDiffAt_oddPeriodPoint_iff f (j.val : ℤ) w hn).mp (hf _)
        simpa only [hj] using hs.contDiffWithinAt (s := Surface.disk)
    · intro n z hz
      obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n
      · rw [seamArc_evenCopyIndex] at hz
        let w : PuncturedClosedDisk k := ⟨⟨z, JacobiFamily.arc_notMem_punctures hz⟩, hz.1.le⟩
        have hj : ((j.val : ℤ) : ZMod m) = j := by simp
        have hs := (R.contMDiffAt_evenPeriodPoint_arc_iff f (j.val : ℤ) w hz).mp (hf _)
        simpa only [hj] using hs
      · rw [seamArc_oddCopyIndex] at hz
        let w : PuncturedClosedDisk k := ⟨⟨z, JacobiFamily.arc_notMem_punctures hz⟩, hz.1.le⟩
        have hj : ((j.val : ℤ) : ZMod m) = j := by simp
        have hs := (R.contMDiffAt_oddPeriodPoint_arc_iff f (j.val : ℤ) w hz).mp (hf _)
        simpa only [hj] using hs
  · intro hf q
    obtain ⟨j, w, rfl | rfl⟩ := R.periodDiskCopies_cover m q
    · rcases lt_or_eq_of_le w.property with hw | hw
      · apply (R.contMDiffAt_evenPeriodPoint_iff f j w hw).mpr
        apply (hf.1 (evenCopyIndex (j : ZMod m))).contDiffAt
        exact (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hw))
      · rcases R.boundary_arc_cases w hw with ha | ha
        · have he : R.oddPeriodPoint m (j-1) w = R.evenPeriodPoint m j w := by
            have hp := (R.odd_even_seam_iff (j-1) w).mpr ha
            have hq := congrArg (HeightLift.periodQuotientMap m) hp
            change R.oddPeriodPoint m (j-1) w = R.evenPeriodPoint m (j-1+1) w at hq
            simpa only [sub_add_cancel] using hq
          rw [← he]
          apply (R.contMDiffAt_oddPeriodPoint_arc_iff f (j-1) w ha).mpr
          apply hf.2.1
          rwa [seamArc_oddCopyIndex]
        · apply (R.contMDiffAt_evenPeriodPoint_arc_iff f j w ha).mpr
          apply hf.2.1
          rwa [seamArc_evenCopyIndex]
    · rcases lt_or_eq_of_le w.property with hw | hw
      · apply (R.contMDiffAt_oddPeriodPoint_iff f j w hw).mpr
        apply (hf.1 (oddCopyIndex (j : ZMod m))).contDiffAt
        exact (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hw))
      · rcases R.boundary_arc_cases w hw with ha | ha
        · apply (R.contMDiffAt_oddPeriodPoint_arc_iff f j w ha).mpr
          apply hf.2.1
          rwa [seamArc_oddCopyIndex]
        · have he : R.evenPeriodPoint m j w = R.oddPeriodPoint m j w :=
            congrArg (HeightLift.periodQuotientMap m) ((R.even_odd_seam_iff j w).mpr ha)
          rw [← he]
          apply (R.contMDiffAt_evenPeriodPoint_arc_iff f j w ha).mpr
          apply hf.2.1
          rwa [seamArc_evenCopyIndex]

/-- The canonical encoding detects the actual compactly supported smooth domain.
This does not assert injectivity for arbitrary unnormalized model families. -/
lemma compactSmooth_iff_encoding_mem_CcSmooth (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    letI := HeightLift.periodChartedSpace R.hC m
    (ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f ∧ HasCompactSupport f) ↔
      encodeDiskFunction (R.diskFunctionPullback f) ∈ Surface.CcSmooth k m := by
  letI := HeightLift.periodChartedSpace R.hC m
  change (_ ∧ _) ↔ Surface.IsSmooth k m _ ∧ Surface.SuppAwayP k m _
  exact and_congr (R.contMDiff_iff_isSmooth_encoding f) (R.hasCompactSupport_iff_suppAwayP f)

end KsIndex.KarcherData.PaperHalfPeriodRealization
