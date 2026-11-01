module

public import KsIndexLean.KarcherSeamCoordinateGerm

@[expose] public section


/-! Uniqueness of unfolded coordinates on the two open sides of a seam.
The totalized planar inversion identifies the two centers at zero, so that
coordinate is explicitly excluded; genuine seam neighborhoods avoid it. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.KarcherData
open scoped QuotientArea
namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

lemma disk_coordinate_ne_reflected_interior {w v : ℂ}
    (hw : ‖w‖ < 1) (hv : ‖v‖ < 1) (hw0 : w ≠ 0) : w ≠ Bracket.σ v := by
  intro he
  have hv0 : v ≠ 0 := by
    intro hz
    exact hw0 (by simpa only [hz, Bracket.σ, map_zero, div_zero] using he)
  have hh := lt_of_not_ge (Bracket.not_norm_σ_le hv0 hv)
  rw [← he] at hh
  exact lt_asymm hw hh

lemma seamPairCoordinate_injOn {n j : ZMod (2*m)} (hnj : n ≠ j) :
    Set.InjOn (R.seamPairCoordinate n)
      ((R.quotientCopyInterior n ∪ R.quotientCopyInterior j) ∩
        {q | R.seamPairCoordinate n q ≠ 0}) := by
  intro x hx y hy he
  rcases hx with ⟨hx, hx0⟩
  rcases hy with ⟨hy, hy0⟩
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    rw [R.seamPairCoordinate_first, R.seamPairCoordinate_first] at he
    exact congrArg (R.orderedDiskPoint n) (Subtype.ext (Subtype.ext he))
  · obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    rw [R.seamPairCoordinate_first, R.seamPairCoordinate_second hnj] at he
    rw [Set.mem_ofPred] at hx0
    rw [R.seamPairCoordinate_first] at hx0
    exact False.elim (disk_coordinate_ne_reflected_interior hw hv hx0 he)
  · obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    rw [R.seamPairCoordinate_second hnj, R.seamPairCoordinate_first] at he
    rw [Set.mem_ofPred] at hy0
    rw [R.seamPairCoordinate_first] at hy0
    exact False.elim (disk_coordinate_ne_reflected_interior hv hw hy0 he.symm)
  · obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    rw [R.seamPairCoordinate_second hnj, R.seamPairCoordinate_second hnj] at he
    have hc : w.val.val = v.val.val := (Function.LeftInverse.injective Bracket.σ_σ) he
    exact congrArg (R.orderedDiskPoint j) (Subtype.ext (Subtype.ext hc))

/-- The exceptional coordinate-zero fiber has zero area on the pair. -/
lemma seamPairCoordinate_zero_null {n j : ZMod (2*m)} (hnj : n ≠ j) :
    ((R.quotientArea).restrict (R.quotientCopyInterior n ∪ R.quotientCopyInterior j))
      {q | R.seamPairCoordinate n q = 0} = 0 := by
  have he := congrArg (fun μ : Measure ℂ => μ {0}) (R.map_seamPairCoordinate_area hnj)
  rw [Measure.map_apply (R.measurable_seamPairCoordinate n) (measurableSet_singleton 0)] at he
  have hz : ewAreaMeasure k {0} = 0 :=
    withDensity_absolutelyContinuous volume _ (measure_singleton (0 : ℂ))
  exact he.trans hz

end PaperHalfPeriodRealization
end KsIndex.KarcherData
