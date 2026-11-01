module

public import KsIndexLean.KarcherCompactProjectionFibers
public import KsIndexLean.KarcherFiniteDeckCovering

@[expose] public section


/-! Compatibility of compact period projection with the regular EW covering. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData
namespace HeightLift
variable {P : Type*} [TopologicalSpace P] {F : P → PeriodTarget}

omit [TopologicalSpace P] in
lemma onePeriodProjection_bijective : Function.Bijective (quotientProjection (F := F) 1) := by
  refine ⟨?_, quotientProjection_surjective 1⟩
  intro x y hxy
  obtain ⟨z,hz⟩ := (same_quotientProjection_iff x y).mp hxy
  have hz0 : z = 0 := Subsingleton.elim _ _
  simpa only [hz0, cyclicDeck_zero] using hz

/-- A single-period EW quotient is homeomorphic to its punctured parameter surface. -/
def onePeriodParameterHomeomorph (hF : Continuous F) : PeriodQuotient F 1 ≃ₜ P :=
  IsHomeomorph.homeomorph _ ⟨(quotientProjection_isLocalHomeomorph hF 1).continuous,
    (quotientProjection_isLocalHomeomorph hF 1).isOpenMap,
    onePeriodProjection_bijective.1, onePeriodProjection_bijective.2⟩
end HeightLift

namespace DiskCompactification
open PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

/-- The compact projection restricts to the complements of the filled ends. -/
def regularPeriodProjection : regularSet (k := k) (m := m) → regularSet (k := k) (m := 1) :=
  fun q => ⟨compactPeriodProjection q.val, by
    change (coordinate (compactPeriodProjection q.val)).val ∉ Surface.punctures k
    rw [compactPeriodProjection_coordinate]
    exact q.property⟩

lemma continuous_regularPeriodProjection :
    Continuous (regularPeriodProjection (k := k) (m := m)) :=
  (continuous_compactPeriodProjection.comp continuous_subtype_val).subtype_mk _

lemma ordered_projection_parity (R : PaperHalfPeriodRealization k)
    (i : ZMod (2 * m)) (w : PuncturedClosedDisk k) :
    HeightLift.quotientProjection 1 (R.orderedDiskPoint (Surface.parity m i) w) =
      HeightLift.quotientProjection m (R.orderedDiskPoint i w) := by
  obtain ⟨j,rfl | rfl⟩ := copyIndex_cases i
  · rw [parity_evenCopyIndex, orderedDiskPoint_even]
    change HeightLift.quotientProjection 1 (R.orderedDiskPoint (evenCopyIndex (0 : ZMod 1)) w) = _
    rw [orderedDiskPoint_even]
    change HeightLift.projection (R.evenDiskPoint _ w) = HeightLift.projection (R.evenDiskPoint _ w)
    rw [R.evenDiskPoint_projection, R.evenDiskPoint_projection]
  · rw [parity_oddCopyIndex, orderedDiskPoint_odd]
    change HeightLift.quotientProjection 1 (R.orderedDiskPoint (oddCopyIndex (0 : ZMod 1)) w) = _
    rw [orderedDiskPoint_odd]
    change HeightLift.projection (R.oddDiskPoint _ w) = HeightLift.projection (R.oddDiskPoint _ w)
    rw [R.oddDiskPoint_projection, R.oddDiskPoint_projection]

lemma regularPeriodProjection_ordered (R : PaperHalfPeriodRealization k)
    (i : ZMod (2 * m)) (w : PuncturedClosedDisk k) :
    regularPeriodProjection (periodQuotientHomeomorph R (R.orderedDiskPoint i w)) =
      periodQuotientHomeomorph R (R.orderedDiskPoint (Surface.parity m i) w) := by
  apply Subtype.ext
  change compactPeriodProjection (periodQuotientHomeomorph R (R.orderedDiskPoint i w)).val = _
  rw [periodQuotientHomeomorph_ordered, periodQuotientHomeomorph_ordered]
  rfl

lemma regularPeriodProjection_compatibility (R : PaperHalfPeriodRealization k)
    (q : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :
    HeightLift.quotientProjection 1 ((periodQuotientHomeomorph R).symm
      (regularPeriodProjection (periodQuotientHomeomorph R q))) =
        HeightLift.quotientProjection m q := by
  obtain ⟨⟨i,w⟩,rfl⟩ := R.orderedDiskPoint_surjective q
  rw [regularPeriodProjection_ordered, Homeomorph.symm_apply_apply]
  exact ordered_projection_parity R i w

/-- Away from the filled ends, period projection is the existing EW covering. -/
theorem regularPeriodProjection_isCoveringMap (R : PaperHalfPeriodRealization k) :
    IsCoveringMap (regularPeriodProjection (k := k) (m := m)) := by
  let H : regularSet (k := k) (m := 1) ≃ₜ ParameterSphere k :=
    (periodQuotientHomeomorph R).symm.trans (HeightLift.onePeriodParameterHomeomorph R.hC)
  have hc := (HeightLift.quotientProjection_isCoveringMap (m := m) R.hC).comp_homeomorph
    (periodQuotientHomeomorph R).symm
  have ht := hc.homeomorph_comp H.symm
  have he : regularPeriodProjection (k := k) (m := m) = H.symm ∘
      (HeightLift.quotientProjection m ∘ (periodQuotientHomeomorph R).symm) := by
    funext x
    apply H.injective
    rw [Function.comp_apply, H.apply_symm_apply]
    change HeightLift.quotientProjection 1 ((periodQuotientHomeomorph R).symm
      (regularPeriodProjection x)) = HeightLift.quotientProjection m
        ((periodQuotientHomeomorph R).symm x)
    simpa only [Homeomorph.apply_symm_apply] using
      regularPeriodProjection_compatibility R ((periodQuotientHomeomorph R).symm x)
  rw [he]
  exact ht

end DiskCompactification
end KsIndex.KarcherData
