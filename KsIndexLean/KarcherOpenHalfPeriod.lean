module

public import KsIndexLean.KarcherHalfPeriodHomeomorph
public import KsIndexLean.OpenSetCompactSupport

@[expose] public section


/-! The actual open height half-period is homeomorphic to the open disk. -/
noncomputable section
open Set Topology
open KsIndex.Surface KsIndex.SurfaceForm
open scoped KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma diskHomeomorph_interior_iff (R : PaperHalfPeriodRealization k)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    ‖(R.diskHomeomorph q).val.val‖ < 1 ↔
      HeightLift.height q.val + Real.pi ∈ Ioo 0 Real.pi := by
  have hp := R.projection_agrees q
  have he := sin_lift_height_shift_pos_iff h.out (reflectionBasepoint k)
    (R.diskHomeomorph q).val rfl R.C q.val hp.symm
  constructor
  · intro hn
    have hs := he.mpr hn
    have hq := q.property
    constructor
    · rcases lt_or_eq_of_le hq.1 with ht | ht
      · exact ht
      · rw [← ht, Real.sin_zero] at hs
        exact False.elim (lt_irrefl _ hs)
    · rcases lt_or_eq_of_le hq.2 with ht | ht
      · exact ht
      · rw [ht, Real.sin_pi] at hs
        exact False.elim (lt_irrefl _ hs)
  · intro hq
    exact he.mp (Real.sin_pos_of_pos_of_lt_pi hq.1 hq.2)

/-- The open geometric half-period, defined by its actual height interval. -/
abbrev OpenHalfPeriod (R : PaperHalfPeriodRealization k) :=
  {q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C //
    HeightLift.height q.val + Real.pi ∈ Ioo 0 Real.pi}

def openDiskMap (R : PaperHalfPeriodRealization k) (q : R.OpenHalfPeriod) : disk :=
  ⟨(R.diskHomeomorph q.val).val.val,
    mem_disk_iff.mpr ((R.diskHomeomorph_interior_iff q.val).mpr q.property)⟩

lemma openDiskMap_isEmbedding (R : PaperHalfPeriodRealization k) :
    IsEmbedding R.openDiskMap := by
  have hv : IsEmbedding (fun w : PuncturedClosedDisk k => w.val.val) :=
    IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have he : IsEmbedding (fun q : R.OpenHalfPeriod => (R.openDiskMap q).val) :=
    (hv.comp R.diskHomeomorph.isEmbedding).comp IsEmbedding.subtypeVal
  exact IsEmbedding.subtypeVal.of_comp_iff.mp he

lemma openDiskMap_surjective (R : PaperHalfPeriodRealization k) :
    Function.Surjective R.openDiskMap := by
  intro z
  let w : PuncturedClosedDisk k :=
    ⟨⟨z.val,punctures_notMem_disk (k := k) (by have := h.out; omega) z.property⟩,
      (mem_disk_iff.mp z.property).le⟩
  have hw : ‖(R.diskHomeomorph (R.diskHomeomorph.symm w)).val.val‖ < 1 := by
    rw [R.diskHomeomorph.apply_symm_apply]
    exact mem_disk_iff.mp z.property
  refine ⟨⟨R.diskHomeomorph.symm w,(R.diskHomeomorph_interior_iff _).mp hw⟩,?_⟩
  apply Subtype.ext
  exact congrArg (fun a : PuncturedClosedDisk k => a.val.val)
    (R.diskHomeomorph.apply_symm_apply w)

/-- Restriction of the geometric disk coordinate to the actual open half-period. -/
def openDiskHomeomorph (R : PaperHalfPeriodRealization k) : R.OpenHalfPeriod ≃ₜ disk :=
  R.openDiskMap_isEmbedding.toHomeomorphOfSurjective R.openDiskMap_surjective

end KsIndex.KarcherData.PaperHalfPeriodRealization
