module

public import KsIndexLean.KarcherConformalCovering

@[expose] public section


/-! The actual closed half-period and punctured closed disk agree topologically. -/
noncomputable section
open Set Topology
open scoped KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData
/-- The closed half-period carries the topology inherited from the actual lift. -/
instance paperHalfPeriodTopology {k : ℕ} (hk : 2 ≤ k) (b : PuncturedPlane k)
    (C : PeriodTarget) : TopologicalSpace (PaperHalfPeriod hk b C) :=
  inferInstanceAs (TopologicalSpace
    {q : PeriodicEWCarrier hk b C // HeightLift.height q + Real.pi ∈ Icc 0 Real.pi})

/-- The disk carries its ordinary subspace topology in the finite parameter plane. -/
instance puncturedClosedDiskTopology (k : ℕ) : TopologicalSpace (PuncturedClosedDisk k) :=
  inferInstanceAs (TopologicalSpace {w : PuncturedPlane k // ‖w.val‖ ≤ 1})

variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The closed half-period fits strictly inside a single open height strip. -/
lemma halfPeriod_mem_strip (C : PeriodTarget)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) C) :
    q.val ∈ HeightLift.strip (-3 * Real.pi / 2) := by
  change HeightLift.height q.val ∈
    Ioo (-3 * Real.pi / 2) (-3 * Real.pi / 2 + 2 * Real.pi)
  have hq := q.property
  constructor <;> linarith [hq.1, hq.2, Real.pi_pos]

/-- Projection on the half-period is an embedding even at its boundary levels. -/
theorem halfPeriod_projection_isEmbedding (C : PeriodTarget)
    (hC : Continuous (extendedEWMap h.out (reflectionBasepoint k) C)) :
    IsEmbedding (fun q : PaperHalfPeriod h.out (reflectionBasepoint k) C =>
      HeightLift.projection q.val) := by
  let i : PaperHalfPeriod h.out (reflectionBasepoint k) C →
      HeightLift.strip (F := extendedEWMap h.out (reflectionBasepoint k) C)
        (-3 * Real.pi / 2) := fun q => ⟨q.val, halfPeriod_mem_strip C q⟩
  have hi : IsEmbedding i :=
    IsEmbedding.subtypeVal.of_comp_iff.mp (show IsEmbedding (Subtype.val ∘ i) from
      IsEmbedding.subtypeVal)
  exact (IsEmbedding.subtypeVal.comp
    (HeightLift.stripHomeomorph hC (-3 * Real.pi / 2)).isEmbedding).comp hi

namespace PaperHalfPeriodRealization

/-- The already chosen disk map is an embedding; no new bijection is chosen. -/
theorem diskMap_isEmbedding (R : PaperHalfPeriodRealization k) :
    IsEmbedding R.diskMap := by
  have he : (fun q => finiteParameter (R.diskMap q).val) =
      (fun q => HeightLift.projection q.val) := funext R.projection_agrees
  have hh : IsEmbedding (fun q => finiteParameter (R.diskMap q).val) := by
    rw [he]
    exact halfPeriod_projection_isEmbedding R.C R.hC
  exact ((isOpenEmbedding_finiteParameter k).isEmbedding.comp
    IsEmbedding.subtypeVal).of_comp_iff.mp hh

/-- The half-period identification is a homeomorphism, including its two
boundary families, with the original diskMap as its forward map. -/
def diskHomeomorph (R : PaperHalfPeriodRealization k) :
    PaperHalfPeriod h.out (reflectionBasepoint k) R.C ≃ₜ PuncturedClosedDisk k :=
  R.diskMap_isEmbedding.toHomeomorphOfSurjective R.disk_bijective.2

@[simp] lemma diskHomeomorph_apply (R : PaperHalfPeriodRealization k)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    R.diskHomeomorph q = R.diskMap q := rfl

lemma diskHomeomorph_symm_projection (R : PaperHalfPeriodRealization k)
    (w : PuncturedClosedDisk k) :
    HeightLift.projection (R.diskHomeomorph.symm w).val = finiteParameter w.val := by
  have he := R.projection_agrees (R.diskHomeomorph.symm w)
  rw [← R.diskHomeomorph_apply] at he
  simpa only [Homeomorph.apply_symm_apply] using he.symm

end PaperHalfPeriodRealization
end KsIndex.KarcherData
