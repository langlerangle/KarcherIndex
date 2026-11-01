module

public import KsIndexLean.KarcherLowerSeamSmooth

@[expose] public section


/-! Smoothness on the interiors of the actual even and odd EW disk copies. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData
open scoped ParameterAtlas
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]
namespace PaperHalfPeriodRealization

lemma baseDiskPoint_height_interior (R : PaperHalfPeriodRealization k)
    (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ < 1) :
    0 < HeightLift.height (R.baseDiskPoint w) + Real.pi ∧
      HeightLift.height (R.baseDiskPoint w) + Real.pi < Real.pi := by
  have hb := (R.diskHomeomorph.symm w).property
  change 0 ≤ HeightLift.height (R.baseDiskPoint w) + Real.pi ∧
    HeightLift.height (R.baseDiskPoint w) + Real.pi ≤ Real.pi at hb
  have h0 : HeightLift.height (R.baseDiskPoint w) + Real.pi ≠ 0 := by
    intro he
    have ha := (halfPeriod_height_zero_iff_arc h.out (reflectionBasepoint k) w.val rfl R.C
      (R.diskHomeomorph.symm w) (R.baseDiskPoint_projection w)).mp he
    exact (ne_of_lt hw) ha.1
  have hpi : HeightLift.height (R.baseDiskPoint w) + Real.pi ≠ Real.pi := by
    intro he
    have ha := (halfPeriod_height_pi_iff_arc h.out (reflectionBasepoint k) w.val rfl R.C
      (R.diskHomeomorph.symm w) (R.baseDiskPoint_projection w)).mp he
    exact (ne_of_lt hw) ha.1
  exact ⟨lt_of_le_of_ne hb.1 (Ne.symm h0), lt_of_le_of_ne hb.2 hpi⟩

lemma evenDiskPoint_mem_upper_interior (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ < 1) :
    R.evenDiskPoint j w ∈ R.upperSeamBand j := by
  have hb := R.baseDiskPoint_height_interior w hw
  change _ < HeightLift.height (R.evenDiskPoint j w) + Real.pi ∧ _
  rw [R.evenDiskPoint_height]
  constructor <;> linarith [Real.pi_pos]

lemma oddDiskPoint_mem_lower_interior (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ < 1) :
    R.oddDiskPoint j w ∈ R.lowerSeamBand j := by
  have hb := R.baseDiskPoint_height_interior w hw
  change _ < HeightLift.height (R.oddDiskPoint j w) + Real.pi ∧ _
  rw [R.oddDiskPoint_height]
  constructor <;> linarith [Real.pi_pos]

lemma glue_interior_germ (u : ZMod (2*m) → ℂ → ℂ) (n : ZMod (2*m))
    {z : ℂ} (hz : ‖z‖ < 1) : Surface.glue u n =ᶠ[𝓝 z] u n := by
  filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_norm continuous_const) hz] with w hw
  exact if_pos (le_of_lt hw)

lemma contMDiffAt_evenPeriodPoint_iff (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (j : ℤ) (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ < 1) :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f (R.evenPeriodPoint m j w) ↔
      ContDiffAt ℝ ∞ (encodeDiskFunction (R.diskFunctionPullback f)
        (evenCopyIndex (j : ZMod m))) w.val.val := by
  letI := HeightLift.periodChartedSpace R.hC m
  have he := R.contMDiffAt_iff_upperSeam_glue f j (R.evenDiskPoint j w) w.val
    (R.evenDiskPoint_mem_upper_interior j w hw) (R.evenDiskPoint_projection j w)
  change ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f (R.evenPeriodPoint m j w) ↔ _ at he
  rw [he]
  have hg := glue_interior_germ (encodeDiskFunction (R.diskFunctionPullback f))
    (evenCopyIndex (j : ZMod m)) hw
  exact ⟨fun hf => hf.congr_of_eventuallyEq hg.symm, fun hf => hf.congr_of_eventuallyEq hg⟩

lemma contMDiffAt_oddPeriodPoint_iff (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (j : ℤ) (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ < 1) :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f (R.oddPeriodPoint m j w) ↔
      ContDiffAt ℝ ∞ (encodeDiskFunction (R.diskFunctionPullback f)
        (oddCopyIndex (j : ZMod m))) w.val.val := by
  letI := HeightLift.periodChartedSpace R.hC m
  have hp : parameterSeamReflection h.out (HeightLift.projection (R.oddDiskPoint j w)) =
      finiteParameter w.val := by
    rw [R.oddDiskPoint_projection, parameterSeamReflection_involutive]
  have he := R.contMDiffAt_iff_lowerSeam_glue f j (R.oddDiskPoint j w) w.val
    (R.oddDiskPoint_mem_lower_interior j w hw) hp
  change ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f (R.oddPeriodPoint m j w) ↔ _ at he
  rw [he]
  have hg := glue_interior_germ (encodeDiskFunction (R.diskFunctionPullback f))
    (oddCopyIndex (j : ZMod m)) hw
  exact ⟨fun hf => hf.congr_of_eventuallyEq hg.symm, fun hf => hf.congr_of_eventuallyEq hg⟩

end PaperHalfPeriodRealization
end KsIndex.KarcherData
