module

public import KsIndexLean.KarcherInfinityAreaChart

@[expose] public section


/-! The quotient area has the actual immersion's local metric density at
 every point, in ordinary or reflected parameter charts. -/
noncomputable section
open Set MeasureTheory Topology
open scoped Topology KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
open scoped QuotientArea
namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

/-- Local geometric compatibility retains the actual ambient immersion and
its actual parameter lift. No arbitrary parametrization or area density is
supplied as an assumption. -/
def HasInducedAreaNeighborhood
    (x : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) : Prop :=
    ∃ q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C,
      HeightLift.periodQuotientMap m q = x ∧
      ((∃ z : ℂ, LocalInducedAreaLaw R.quotientArea (R.centeredChart q)
          (HeightLift.periodChart R.hC m x).symm z x) ∨
       ∃ w : PuncturedPlane k, LocalInducedAreaLaw R.quotientArea
          (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift q w)
          (HeightLift.periodQuotientMap m ∘ R.lowerParameterLift q w) w.val x)

/-- The candidate quotient area is locally induced by the actual EW immersion
throughout the quotient. This includes both seam families, the cyclic seam,
all finite interiors, and every infinity point. -/
theorem quotientArea_hasInducedAreaNeighborhood
    (x : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :
    R.HasInducedAreaNeighborhood x := by
  by_cases hs : x ∈ R.quotientSeams
  · obtain ⟨q, w, hqx, hw, hp, hu | hl⟩ := R.quotientSeam_localInducedAreaLaw x hs
    · exact ⟨q, hqx, Or.inl ⟨w.val, hu⟩⟩
    · exact ⟨q, hqx, Or.inr ⟨w, hl⟩⟩
  · obtain ⟨⟨n,w⟩, rfl⟩ := R.orderedDiskPoint_surjective x
    have hwne : ‖w.val.val‖ ≠ 1 :=
      fun hw => hs ((R.orderedDiskPoint_mem_quotientSeams n w).mpr hw)
    have hw : ‖w.val.val‖ < 1 := lt_of_le_of_ne w.property hwne
    obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n
    · change R.HasInducedAreaNeighborhood (R.orderedDiskPoint (evenCopyIndex j) w)
      rw [R.orderedDiskPoint_even]
      refine ⟨R.evenDiskPoint j.val w, rfl, Or.inl ⟨w.val.val, ?_⟩⟩
      exact R.upperSeam_localInducedAreaLaw j.val (R.evenDiskPoint j.val w) w.val
        (R.evenDiskPoint_mem_upper_interior j.val w hw) (R.evenDiskPoint_projection j.val w)
    · change R.HasInducedAreaNeighborhood (R.orderedDiskPoint (oddCopyIndex j) w)
      rw [R.orderedDiskPoint_odd]
      refine ⟨R.oddDiskPoint j.val w, rfl, ?_⟩
      by_cases hz : w.val.val = 0
      · exact Or.inl ⟨0, R.infinity_localInducedAreaLaw j w hz⟩
      · apply Or.inr
        refine ⟨w.val, R.lowerSeam_localInducedAreaLaw j.val (R.oddDiskPoint j.val w) w.val hz
          (R.oddDiskPoint_mem_lower_interior j.val w hw) ?_⟩
        rw [R.oddDiskPoint_projection, parameterSeamReflection_involutive]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
