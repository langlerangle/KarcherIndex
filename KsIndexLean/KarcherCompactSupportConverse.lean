module

public import KsIndexLean.KarcherDiskSupport

@[expose] public section


/-! Compact subsets of the EW quotient stay uniformly away from deleted ends
in the folded disk coordinate. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

/-- Fold the disk copies onto their common disk parameter. This is continuous,
including across seams, but is not asserted to be a smooth chart. -/
def foldedDiskCoordinate (R : PaperHalfPeriodRealization k) :
    HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ :=
  R.diskFunctionDescend ⟨fun p => p.2.val.val, fun _ _ _ => rfl⟩

lemma foldedDiskCoordinate_apply (R : PaperHalfPeriodRealization k)
    (n : ZMod (2 * m)) (w : PuncturedClosedDisk k) :
    R.foldedDiskCoordinate (R.orderedDiskPoint n w) = w.val.val :=
  R.diskFunctionDescend_apply _ (n,w)

lemma continuous_foldedDiskCoordinate (R : PaperHalfPeriodRealization k) :
    Continuous (R.foldedDiskCoordinate (m := m)) := by
  apply (R.continuous_diskFunctionDescend_iff _).mpr
  have he : IsEmbedding (fun w : PuncturedClosedDisk k => w.val.val) :=
    IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  exact he.continuous.comp continuous_snd

lemma foldedDiskCoordinate_not_puncture (R : PaperHalfPeriodRealization k)
    (q : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :
    R.foldedDiskCoordinate q ∉ Surface.punctures k := by
  obtain ⟨⟨n,w⟩, rfl⟩ := R.orderedDiskPoint_surjective q
  rw [foldedDiskCoordinate_apply]
  exact w.val.property

lemma compact_uniform_puncture_distance (R : PaperHalfPeriodRealization k)
    (K : Set (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m))
    (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ K, ∀ p ∈ Surface.punctures k,
      ε < ‖R.foldedDiskCoordinate q - p‖ := by
  have hc := hK.image R.continuous_foldedDiskCoordinate
  have hp : IsClosed (Surface.punctures k) :=
    isClosed_eq (continuous_id.pow (2 * k)) continuous_const
  have hd : Disjoint (R.foldedDiskCoordinate '' K) (Surface.punctures k) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨q, hq, rfl⟩ hz
    exact R.foldedDiskCoordinate_not_puncture q hz
  obtain ⟨ε, hε, he⟩ := Metric.exists_pos_forall_lt_edist hc hp hd
  refine ⟨ε, hε, fun q hq p hp => ?_⟩
  have hh := he _ ⟨q, hq, rfl⟩ p hp
  simpa only [edist_nndist, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe,
    coe_nndist, dist_eq_norm] using hh

lemma suppAwayP_of_hasCompactSupport (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hf : HasCompactSupport f) :
    Surface.SuppAwayP k m (encodeDiskFunction (R.diskFunctionPullback f)) := by
  obtain ⟨ε, hε, he⟩ := R.compact_uniform_puncture_distance (tsupport f) hf
  refine ⟨ε, hε, fun n w hw => ?_⟩
  classical
  unfold encodeDiskFunction
  split_ifs with hd
  · let v : PuncturedClosedDisk k := ⟨⟨w, hd.1⟩, hd.2⟩
    change f (R.orderedDiskPoint n v) = 0
    by_contra hn
    have ht : R.orderedDiskPoint n v ∈ tsupport f := subset_tsupport f hn
    obtain ⟨p, hp, hwp⟩ := hw
    have hh := he _ ht p hp
    rw [foldedDiskCoordinate_apply] at hh
    exact (not_lt_of_ge hh.le) hwp
  · rfl

/-- Geometric compact support is exactly the paper's puncture-neighborhood
vanishing condition for the canonical total encoding. -/
lemma hasCompactSupport_iff_suppAwayP (R : PaperHalfPeriodRealization k)
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    HasCompactSupport f ↔
      Surface.SuppAwayP k m (encodeDiskFunction (R.diskFunctionPullback f)) := by
  constructor
  · exact R.suppAwayP_of_hasCompactSupport f
  · intro hf
    have hc := R.hasCompactSupport_descend_of_suppAwayP _
      (encodeDiskFunction_seamVal (R.diskFunctionPullback f)) hf
    rw [restrict_encodeDiskFunction] at hc
    have he : R.diskFunctionDescend (R.diskFunctionPullback f) = f :=
      R.diskFunctionEquiv.symm_apply_apply f
    rwa [he] at hc

end KsIndex.KarcherData.PaperHalfPeriodRealization
