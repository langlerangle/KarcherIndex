module

public import KsIndexLean.DiskExtensionCompact
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

@[expose] public section


noncomputable section
open Set MeasureTheory TopologicalSpace TauCeti
open scoped ENNReal Topology
namespace KsIndex.WeakH1
open KsIndex.Trace

/-- Restriction of a whole-plane L2 class to the actual disk measure. -/
def restrictPlaneL2 (f : Lp ℂ 2 (volume : Measure ℂ)) : L2C :=
  ((Lp.memLp f).restrict (disk : Set ℂ)).toLp f

lemma restrictPlaneL2_ae (f : Lp ℂ 2 (volume : Measure ℂ)) :
    restrictPlaneL2 f =ᵐ[volume.restrict (disk : Set ℂ)] f :=
  ((Lp.memLp f).restrict (disk : Set ℂ)).coeFn_toLp

lemma restrictPlaneL2_lipschitz : LipschitzWith 1 restrictPlaneL2 := by
  intro f g
  simp only [ENNReal.coe_one, one_mul]
  rw [Lp.edist_def, Lp.edist_def]
  have he : eLpNorm (⇑(restrictPlaneL2 f) - ⇑(restrictPlaneL2 g)) 2
      (volume.restrict (disk : Set ℂ)) =
      eLpNorm (⇑f - ⇑g) 2 (volume.restrict (disk : Set ℂ)) := by
    apply eLpNorm_congr_ae
    filter_upwards [restrictPlaneL2_ae f, restrictPlaneL2_ae g] with z hz hgz
    simp only [Pi.sub_apply, hz, hgz]
  rw [he]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

lemma restrictPlaneL2_extension (u : ComplexH1) :
    restrictPlaneL2 (diskExtensionLp u) = valueCLM u := by
  apply Lp.ext
  have he : diskExtensionLp u =ᵐ[volume.restrict (disk : Set ℂ)] cutoffDiskExtension u :=
    (diskExtensionLp_ae u).filter_mono (ae_mono Measure.restrict_le_self)
  filter_upwards [restrictPlaneL2_ae (diskExtensionLp u), he,
    ae_restrict_mem disk.isOpen.measurableSet] with z hz hez hzin
  rw [hz, hez, cutoffDiskExtension_eq_inner u hzin]

/-- The unrestricted complex disk H1-to-L2 inclusion is compact. -/
theorem valueCLM_isCompactOperator : IsCompactOperator valueCLM := by
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  refine ⟨{u : ComplexH1 | ‖u‖ ≤ 1}, ?_,
    restrictPlaneL2 '' closure (diskExtensionLp '' {u : ComplexH1 | ‖u‖ ≤ 1}),
    diskExtensionLp_unitBall_relativelyCompact.image restrictPlaneL2_lipschitz.continuous, ?_⟩
  · have he : {u : ComplexH1 | ‖u‖ ≤ 1} = Metric.closedBall 0 1 := by
      ext u
      simp
    rw [he]
    exact Metric.closedBall_mem_nhds _ (by norm_num)
  · rintro f ⟨u, hu, rfl⟩
    exact ⟨diskExtensionLp u, subset_closure ⟨u, hu, rfl⟩, restrictPlaneL2_extension u⟩

end KsIndex.WeakH1
