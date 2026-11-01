module

public import KsIndexLean.KarcherDiskInteriorSmooth

@[expose] public section


/-! Actual smoothness at each of the two alternating seam families. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData
open scoped ParameterAtlas
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]
namespace PaperHalfPeriodRealization

lemma boundary_arc_cases (R : PaperHalfPeriodRealization k)
    (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ = 1) :
    w.val.val ∈ Surface.arc k 0 ∨ w.val.val ∈ Surface.arc k 1 := by
  have hz := halfPeriod_height_zero_iff_arc h.out (reflectionBasepoint k) w.val rfl R.C
    (R.diskHomeomorph.symm w) (R.baseDiskPoint_projection w)
  have hp := halfPeriod_height_pi_iff_arc h.out (reflectionBasepoint k) w.val rfl R.C
    (R.diskHomeomorph.symm w) (R.baseDiskPoint_projection w)
  exact (halfPeriod_boundary_levels h.out (reflectionBasepoint k) w.val rfl R.C
    (R.diskHomeomorph.symm w) (R.baseDiskPoint_projection w) hw).imp hz.mp hp.mp

lemma evenDiskPoint_mem_upper_arc (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) (hw : w.val.val ∈ Surface.arc k 1) :
    R.evenDiskPoint j w ∈ R.upperSeamBand j := by
  have hp := (halfPeriod_height_pi_iff_arc h.out (reflectionBasepoint k) w.val rfl R.C
    (R.diskHomeomorph.symm w) (R.baseDiskPoint_projection w)).mpr hw
  change _ < HeightLift.height (R.evenDiskPoint j w) + Real.pi ∧ _
  change HeightLift.height (R.baseDiskPoint w) + Real.pi = Real.pi at hp
  rw [R.evenDiskPoint_height, hp]
  constructor <;> linarith [Real.pi_pos]

lemma oddDiskPoint_mem_lower_arc (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) (hw : w.val.val ∈ Surface.arc k 0) :
    R.oddDiskPoint j w ∈ R.lowerSeamBand j := by
  have hp := (halfPeriod_height_zero_iff_arc h.out (reflectionBasepoint k) w.val rfl R.C
    (R.diskHomeomorph.symm w) (R.baseDiskPoint_projection w)).mpr hw
  change _ < HeightLift.height (R.oddDiskPoint j w) + Real.pi ∧ _
  change HeightLift.height (R.baseDiskPoint w) + Real.pi = 0 at hp
  rw [R.oddDiskPoint_height, hp]
  constructor <;> linarith [Real.pi_pos]

lemma contMDiffAt_evenPeriodPoint_arc_iff (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (j : ℤ) (w : PuncturedClosedDisk k) (hw : w.val.val ∈ Surface.arc k 1) :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f (R.evenPeriodPoint m j w) ↔
      ContDiffAt ℝ ∞ (Surface.glue (encodeDiskFunction (R.diskFunctionPullback f))
        (evenCopyIndex (j : ZMod m))) w.val.val :=
  R.contMDiffAt_iff_upperSeam_glue f j (R.evenDiskPoint j w) w.val
    (R.evenDiskPoint_mem_upper_arc j w hw) (R.evenDiskPoint_projection j w)

lemma contMDiffAt_oddPeriodPoint_arc_iff (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (j : ℤ) (w : PuncturedClosedDisk k) (hw : w.val.val ∈ Surface.arc k 0) :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f (R.oddPeriodPoint m j w) ↔
      ContDiffAt ℝ ∞ (Surface.glue (encodeDiskFunction (R.diskFunctionPullback f))
        (oddCopyIndex (j : ZMod m))) w.val.val := by
  apply R.contMDiffAt_iff_lowerSeam_glue f j (R.oddDiskPoint j w) w.val
    (R.oddDiskPoint_mem_lower_arc j w hw)
  rw [R.oddDiskPoint_projection, parameterSeamReflection_involutive]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
