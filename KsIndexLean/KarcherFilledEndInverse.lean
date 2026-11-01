module

public import KsIndexLean.KarcherFoldedFiniteParameter

@[expose] public section


/-! The root-chart inverse extended to the added endpoint. -/
noncomputable section
open Set Topology Filter
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]
variable (R : PaperHalfPeriodRealization k) {w : ℂ} (hw : w ∈ Surface.punctures k)

abbrev EndRegion := filledEndRootRegion h.out hw (reflectionBasepoint k) (m := m)

def endCenter : EndRegion (m := m) hw :=
  ⟨0, zero_mem_filledEndRootRegion h.out (NeZero.pos m) hw (reflectionBasepoint k)⟩

/-- At nonzero roots use the existing end-chart inverse; at zero add its vertex. -/
def filledEndInverse (t : EndRegion (m := m) hw) : FilledChain k m := by
  classical
  exact if ht : t.val = 0 then vertex w hw else
    (periodQuotientHomeomorph R
      ((quotientEndHomeomorph h.out (NeZero.pos m) hw (reflectionBasepoint k) R.C R.hC).symm
        ⟨t.val, by
          rw [quotientEndTarget_eq h.out (NeZero.pos m) hw (reflectionBasepoint k)]
          exact ⟨t.property, ht⟩⟩).val).val

@[simp] lemma filledEndInverse_center :
    filledEndInverse R hw (endCenter (m := m) hw) = vertex w hw := by
  simp [filledEndInverse, endCenter]

/-- A single continuous coordinate formula holds both at and off the center. -/
lemma coordinate_filledEndInverse (t : EndRegion (m := m) hw) :
    (coordinate (filledEndInverse R hw t)).val =
      foldUnitDisk (filledEndParameter h.out hw (reflectionBasepoint k) (m := m) t.val) := by
  classical
  by_cases ht : t.val = 0
  · simp [filledEndInverse, ht, filledEndParameter_zero h.out (NeZero.pos m),
      foldUnitDisk_of_norm_one (puncture_norm h.out hw)]
  · let u : quotientEndTarget h.out hw (reflectionBasepoint k) (m := m) :=
      ⟨t.val, by
        rw [quotientEndTarget_eq h.out (NeZero.pos m) hw (reflectionBasepoint k)]
        exact ⟨t.property, ht⟩⟩
    let e := quotientEndHomeomorph h.out (NeZero.pos m) hw (reflectionBasepoint k) R.C R.hC
    let q := e.symm u
    obtain ⟨z, hz, hp⟩ := q.property
    have he : quotientEndRoot h.out (NeZero.pos m) (reflectionBasepoint k) w R.C q.val =
        t.val := congrArg Subtype.val (e.apply_symm_apply u)
    have ha := filledEndParameter_quotientEndRoot h.out (NeZero.pos m) hw
      (reflectionBasepoint k) R.C q.val z hz hp
    rw [he] at ha
    simp only [filledEndInverse, dite_eq_right ht, coordinate_periodQuotientHomeomorph]
    change R.foldedDiskCoordinate q.val = _
    rw [R.foldedDiskCoordinate_finite q.val z hp, ha]

/-- The extended inverse is continuous at its center in the actual compact
quotient topology. -/
theorem continuousAt_filledEndInverse_center :
    ContinuousAt (filledEndInverse R hw) (endCenter (m := m) hw) := by
  change Tendsto (filledEndInverse R hw) (𝓝 (endCenter hw))
    (𝓝 (filledEndInverse R hw (endCenter hw)))
  rw [filledEndInverse_center, tendsto_vertex_iff]
  have he : (fun t : EndRegion (m := m) hw => (coordinate (filledEndInverse R hw t)).val) =
      (fun t => foldUnitDisk
        (filledEndParameter h.out hw (reflectionBasepoint k) (m := m) t.val)) :=
    funext (coordinate_filledEndInverse R hw)
  rw [he]
  have hc := continuousOn_iff_continuous_domRestrict.mp
    (continuousOn_filledEndParameter h.out hw (reflectionBasepoint k) (m := m))
  have hh := (continuous_foldUnitDisk.comp hc).continuousAt (x := endCenter (m := m) hw)
  simpa only [ContinuousAt, Function.comp_def, Set.domRestrict_apply, endCenter,
    filledEndParameter_zero h.out (NeZero.pos m),
    foldUnitDisk_of_norm_one (puncture_norm h.out hw)] using hh

lemma filledEndInverse_mem_regular_iff (t : EndRegion (m := m) hw) :
    filledEndInverse R hw t ∈ regularSet ↔ t.val ≠ 0 := by
  classical
  by_cases ht : t.val = 0
  · simp [filledEndInverse, ht, regularSet, coordinate_vertex, hw]
  · simp only [filledEndInverse, dite_eq_right ht]
    exact iff_of_true (Subtype.property _) ht

/-- Filling the center does not identify two distinct root coordinates. -/
theorem filledEndInverse_injective : Function.Injective (filledEndInverse R (m := m) hw) := by
  classical
  intro t u he
  by_cases ht : t.val = 0
  · have hu : u.val = 0 := by
      by_contra hu
      have hh := (filledEndInverse_mem_regular_iff R hw u).mpr hu
      rw [← he, filledEndInverse_mem_regular_iff] at hh
      exact hh ht
    exact Subtype.ext (ht.trans hu.symm)
  · have hu : u.val ≠ 0 := by
      have hh := (filledEndInverse_mem_regular_iff R hw t).mpr ht
      rw [he, filledEndInverse_mem_regular_iff] at hh
      exact hh
    simp only [filledEndInverse, dite_eq_right ht, dite_eq_right hu] at he
    have he1 := (periodQuotientHomeomorph R).injective (Subtype.ext he)
    have he2 := (quotientEndHomeomorph h.out (NeZero.pos m) hw
      (reflectionBasepoint k) R.C R.hC).symm.injective (Subtype.ext he1)
    exact Subtype.ext (congrArg
      (fun x : quotientEndTarget h.out hw (reflectionBasepoint k) (m := m) => x.val) he2)

/-- The zero-extended root inverse is continuous on its whole root region. -/
theorem continuous_filledEndInverse : Continuous (filledEndInverse R (m := m) hw) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t.val = 0
  · have he : t = endCenter hw := Subtype.ext ht
    rw [he]
    exact continuousAt_filledEndInverse_center R hw
  · let S : Set (EndRegion (m := m) hw) := {u | u.val ≠ 0}
    have hS : IsOpen S := (isClosed_eq continuous_subtype_val continuous_const).isOpen_compl
    have hc : ContinuousOn (filledEndInverse R hw) S := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      let g : S → quotientEndTarget h.out hw (reflectionBasepoint k) (m := m) :=
        fun u => ⟨u.val.val, by
          rw [quotientEndTarget_eq h.out (NeZero.pos m) hw (reflectionBasepoint k)]
          exact ⟨u.val.property, u.property⟩⟩
      have hg : Continuous g := by fun_prop
      have he : (S.domRestrict (filledEndInverse R hw)) = (fun u =>
          (periodQuotientHomeomorph R
            ((quotientEndHomeomorph h.out (NeZero.pos m) hw (reflectionBasepoint k)
              R.C R.hC).symm (g u)).val).val) := by
        funext u
        simp only [Set.domRestrict_apply, filledEndInverse, dite_eq_right u.property]
        rfl
      rw [he]
      exact continuous_subtype_val.comp ((periodQuotientHomeomorph R).continuous.comp
        (continuous_subtype_val.comp
          ((quotientEndHomeomorph h.out (NeZero.pos m) hw (reflectionBasepoint k)
            R.C R.hC).symm.continuous.comp hg)))
    exact hc.continuousAt (hS.mem_nhds ht)

/-- Restriction of the extended inverse to any closed disk inside its root region. -/
def closedEndInverse (r : ℝ) (hr : Metric.closedBall (0 : ℂ) r ⊆ EndRegion (m := m) hw) :
    Metric.closedBall (0 : ℂ) r → FilledChain k m :=
  fun t => filledEndInverse R hw ⟨t.val, hr t.property⟩

lemma closedEndInverse_isClosedEmbedding (r : ℝ)
    (hr : Metric.closedBall (0 : ℂ) r ⊆ EndRegion (m := m) hw) :
    Topology.IsClosedEmbedding (closedEndInverse R hw r hr) := by
  have : CompactSpace (Metric.closedBall (0 : ℂ) r) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) r)
  apply Continuous.isClosedEmbedding
  · exact (continuous_filledEndInverse R hw).comp (by fun_prop)
  · intro t u he
    have hh := filledEndInverse_injective R hw he
    exact Subtype.ext (congrArg (fun x : EndRegion (m := m) hw => x.val) hh)

/-- A closed root disk is homeomorphic to its image in the compactification,
including its filled center. The conclusion concerns the range with its subspace
topology; it does not assert that this range is a neighborhood of the center. -/
def closedEndHomeomorph (r : ℝ)
    (hr : Metric.closedBall (0 : ℂ) r ⊆ EndRegion (m := m) hw) :
    Metric.closedBall (0 : ℂ) r ≃ₜ Set.range (closedEndInverse R hw r hr) :=
  (closedEndInverse_isClosedEmbedding R hw r hr).isEmbedding.toHomeomorph

lemma exists_closedEndDisk : ∃ r : ℝ, 0 < r ∧
    Metric.closedBall (0 : ℂ) r ⊆ EndRegion (m := m) hw := by
  obtain ⟨ε, hε, hs⟩ := Metric.isOpen_iff.mp
    (isOpen_filledEndRootRegion h.out hw (reflectionBasepoint k) (m := m)) 0
    (zero_mem_filledEndRootRegion h.out (NeZero.pos m) hw (reflectionBasepoint k))
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro z hz
  apply hs
  exact lt_of_le_of_lt hz (half_lt_self hε)

end KsIndex.KarcherData.DiskCompactification
