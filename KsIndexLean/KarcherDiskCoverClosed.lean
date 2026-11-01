module

public import KsIndexLean.KarcherDiskCopyTopology
public import Mathlib.Topology.Order.AtTopBotIxx

@[expose] public section


/-! Closed sets can be tested on the locally finite closed disk cover of the EW carrier. -/
noncomputable section
open Set Topology Filter
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma diskBands_locallyFinite (R : PaperHalfPeriodRealization k) :
    LocallyFinite (fun j : ℤ => {q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C |
      HeightLift.height q + Real.pi ∈ Icc ((j : ℝ) * (2 * Real.pi))
        ((j : ℝ) * (2 * Real.pi) + 2 * Real.pi)}) := by
  have hp : 0 < 2 * Real.pi := by positivity
  have ht : Tendsto (fun j : ℤ => (j : ℝ) * (2 * Real.pi)) atTop atTop :=
    tendsto_intCast_atTop_atTop.atTop_mul_const hp
  have hb : Tendsto (fun j : ℤ => (j : ℝ) * (2 * Real.pi)) atBot atBot :=
    (tendsto_intCast_atBot_iff.mpr tendsto_id).atBot_mul_const hp
  have hb' : Tendsto (fun j : ℤ => (j : ℝ) * (2 * Real.pi) + 2 * Real.pi) atBot atBot :=
    tendsto_atBot_add_const_right _ _ hb
  exact (locallyFinite_Icc_of_tendsto ht hb').preimage_continuous
    (HeightLift.continuous_height.add continuous_const)

lemma isClosed_of_disk_preimages (R : PaperHalfPeriodRealization k)
    (A : Set (PeriodicEWCarrier h.out (reflectionBasepoint k) R.C))
    (he : ∀ j : ℤ, IsClosed (R.evenDiskPoint j ⁻¹' A))
    (ho : ∀ j : ℤ, IsClosed (R.oddDiskPoint j ⁻¹' A)) : IsClosed A := by
  let E := fun j : ℤ => R.evenDiskPoint j '' (R.evenDiskPoint j ⁻¹' A) ∪
    R.oddDiskPoint j '' (R.oddDiskPoint j ⁻¹' A)
  have hclosed : ∀ j, IsClosed (E j) := fun j =>
    ((R.evenDiskPoint_isClosedEmbedding j).isClosedMap _ (he j)).union
      ((R.oddDiskPoint_isClosedEmbedding j).isClosedMap _ (ho j))
  have hloc : LocallyFinite E := R.diskBands_locallyFinite.subset (by
    intro j q hq
    rcases hq with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
    · have hh := R.evenDiskPoint_height_mem j w
      exact ⟨hh.1, by linarith [hh.2, Real.pi_pos]⟩
    · have hh := R.oddDiskPoint_height_mem j w
      exact ⟨by linarith [hh.1, Real.pi_pos], hh.2⟩)
  have hcover : (⋃ j, E j) = A := by
    ext q
    constructor
    · intro hq
      obtain ⟨j, hj⟩ := mem_iUnion.mp hq
      rcases hj with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩ <;> exact hw
    · intro hq
      obtain ⟨j, w, rfl | rfl⟩ := R.diskCopies_cover q
      · exact mem_iUnion.mpr ⟨j, Or.inl ⟨w, hq, rfl⟩⟩
      · exact mem_iUnion.mpr ⟨j, Or.inr ⟨w, hq, rfl⟩⟩
  rw [← hcover]
  exact hloc.isClosed_iUnion hclosed

end KsIndex.KarcherData.PaperHalfPeriodRealization
