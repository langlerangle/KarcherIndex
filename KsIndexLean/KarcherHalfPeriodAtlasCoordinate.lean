module

public import KsIndexLean.KarcherHalfPeriodClassical
public import KsIndexLean.KarcherDirichletTestSpace

@[expose] public section


/-! The half-period disk coordinate is the actual finite coordinate of the
registered lift atlas, including at the physical boundary. -/
noncomputable section
open scoped KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

theorem halfPeriod_liftChart_coordinate (R : PaperHalfPeriodRealization k)
    (q r : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    HeightLift.liftChart R.hC q.val r.val = (R.diskHomeomorph r).val.val := by
  rw [HeightLift.liftChart_apply,← R.projection_agrees q,← R.projection_agrees r]
  change chartAt ℂ (Spherical.sphereChart (R.diskHomeomorph q).val.val)
    (Spherical.sphereChart (R.diskHomeomorph r).val.val) = _
  rw [ParameterAtlas.sphere_chartAt_finite,ParameterAtlas.finite_apply]

theorem halfPeriod_chartCenter_coordinate (R : PaperHalfPeriodRealization k)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    R.chartCenter q.val = (R.diskHomeomorph q).val.val :=
  R.halfPeriod_liftChart_coordinate q q

theorem openHalfPeriod_liftChart_coordinate (R : PaperHalfPeriodRealization k)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) (r : R.OpenHalfPeriod) :
    HeightLift.liftChart R.hC q.val r.val.val = (R.openDiskHomeomorph r).val := by
  rw [R.halfPeriod_liftChart_coordinate]
  simp only [openDiskHomeomorph,Topology.IsEmbedding.toHomeomorphOfSurjective_apply,
    openDiskMap]

end KsIndex.KarcherData.PaperHalfPeriodRealization
