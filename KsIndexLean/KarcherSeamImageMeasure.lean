module

public import KsIndexLean.KarcherSeamInverseMeasure

@[expose] public section


/-! Identification of the two-copy measure restriction with the full image
of a local seam parametrization, using nullity of the actual seam locus. -/
noncomputable section
open Set MeasureTheory Topology
namespace KsIndex.KarcherData
open scoped QuotientArea
namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

lemma closedSeamPair_mem_interiors_of_not_seam {n : ZMod (2*m)}
    {x : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m}
    (hx : x ∈ R.closedSeamPair n) (hs : x ∉ R.quotientSeams) :
    x ∈ R.quotientCopyInterior n ∪ R.quotientCopyInterior (n+1) := by
  rcases hx with ⟨w,rfl⟩ | ⟨w,rfl⟩
  · have hw : ‖w.val.val‖ ≠ 1 := fun hw => hs ((R.orderedDiskPoint_mem_quotientSeams n w).mpr hw)
    exact Or.inl ⟨w, lt_of_le_of_ne w.property hw, rfl⟩
  · have hw : ‖w.val.val‖ ≠ 1 := fun hw => hs ((R.orderedDiskPoint_mem_quotientSeams (n+1) w).mpr hw)
    exact Or.inr ⟨w, lt_of_le_of_ne w.property hw, rfl⟩

lemma seamPairCoordinate_norm_ne_one {n : ZMod (2*m)}
    {x : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m}
    (hx : x ∈ R.quotientCopyInterior n ∪ R.quotientCopyInterior (n+1)) :
    ‖R.seamPairCoordinate n x‖ ≠ 1 := by
  rcases hx with ⟨w,hw,rfl⟩ | ⟨w,hw,rfl⟩
  · rw [R.seamPairCoordinate_first]
    exact ne_of_lt hw
  · rw [R.seamPairCoordinate_second (copyIndex_ne_successor n), Bracket.norm_σ]
    intro he
    have hh := congrArg (fun t : ℝ => t⁻¹) he
    rw [inv_inv, inv_one] at hh
    exact (ne_of_lt hw) hh

lemma restrict_pair_preimage_eq_image (n : ZMod (2*m)) {U : Set ℂ} (hU : MeasurableSet U)
    (g : ℂ → HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m)
    (hsupport : ∀ z ∈ U, g z ∈ R.closedSeamPair n)
    (hcoord : ∀ z ∈ U, R.seamPairCoordinate n (g z) = z)
    (hinv : ∀ z ∈ U, ∀ x,
      x ∈ R.quotientCopyInterior n ∪ R.quotientCopyInterior (n+1) →
      R.seamPairCoordinate n x = z → z ≠ 0 → ‖z‖ ≠ 1 → g z = x) :
    ((R.quotientArea).restrict
      (R.quotientCopyInterior n ∪ R.quotientCopyInterior (n+1))).restrict
      (R.seamPairCoordinate n ⁻¹' U) = (R.quotientArea).restrict (g '' U) := by
  have hpair := ((R.isOpen_quotientCopyInterior n).union
    (R.isOpen_quotientCopyInterior (n+1))).measurableSet
  have hz : ∀ᵐ x ∂(R.quotientArea).restrict
      (R.quotientCopyInterior n ∪ R.quotientCopyInterior (n+1)),
      R.seamPairCoordinate n x ≠ 0 :=
    ae_iff.mpr (by simpa only [not_not] using
      R.seamPairCoordinate_zero_null (copyIndex_ne_successor n))
  have hz' := (ae_restrict_iff' hpair).mp hz
  have hs : ∀ᵐ x ∂(R.quotientArea), x ∉ R.quotientSeams :=
    ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using R.quotientArea_seams_null (m := m))
  rw [Measure.restrict_restrict ((R.measurable_seamPairCoordinate n) hU)]
  apply Measure.restrict_congr_set
  filter_upwards [hz', hs] with x hx0 hxs
  apply propext
  constructor
  · rintro ⟨hxu,hxp⟩
    exact ⟨R.seamPairCoordinate n x, hxu,
      hinv _ hxu x hxp rfl (hx0 hxp) (R.seamPairCoordinate_norm_ne_one hxp)⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨by change R.seamPairCoordinate n (g z) ∈ U; rw [hcoord z hz]; exact hz,
      R.closedSeamPair_mem_interiors_of_not_seam (hsupport z hz) hxs⟩

end PaperHalfPeriodRealization
end KsIndex.KarcherData
