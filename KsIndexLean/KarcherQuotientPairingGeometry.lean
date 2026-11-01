module

public import KsIndexLean.KarcherQuotientPairing
public import KsIndexLean.KarcherCopyPairingGeometry

@[expose] public section


/-! The assembled quotient Jacobi density is the actual mixed metric-gradient
pairing minus the actual curvature potential, away from a proved null set. -/
noncomputable section
open Set MeasureTheory
open scoped KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
open scoped QuotientArea
namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)
  (G H : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)

lemma quotientJacobiDensity_even_geometry (j : ZMod m) (w : PuncturedClosedDisk k)
    (hw : ‖w.val.val‖ < 1) :
    let x := R.orderedDiskPoint (evenCopyIndex j) w
    R.quotientJacobiDensity G H x =
      chartInvMetricGradInner (R.centeredChart (R.evenDiskPoint j.val w))
        (G ∘ (HeightLift.periodChart R.hC m x).symm)
        (H ∘ (HeightLift.periodChart R.hC m x).symm) w.val.val -
      (R.quotientAbsA x ^ 2 : ℝ) • ((starRingEnd ℂ) (G x) * H x) := by
  dsimp only
  rw [quotientJacobiDensity, R.assembleCopyDensity_ordered _ _ w hw]
  unfold copyJacobiDensity
  rw [R.orderedDiskPoint_even, R.evenCopy_inverseMetricPairing G H j.val w hw]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← R.orderedDiskPoint_even j w, quotientAbsA, R.diskCoordinate_orderedDiskPoint,
    encodeDiskFunction_on_disk, encodeDiskFunction_on_disk]
  rfl

lemma quotientJacobiDensity_odd_geometry (j : ZMod m) (w : PuncturedClosedDisk k)
    (hw : ‖w.val.val‖ < 1) (hw0 : w.val.val ≠ 0) :
    let x := R.orderedDiskPoint (oddCopyIndex j) w
    R.quotientJacobiDensity G H x =
      chartInvMetricGradInner
        (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift (R.oddDiskPoint j.val w) w.val)
        (fun z => G (HeightLift.periodQuotientMap m (R.lowerParameterLift (R.oddDiskPoint j.val w) w.val z)))
        (fun z => H (HeightLift.periodQuotientMap m (R.lowerParameterLift (R.oddDiskPoint j.val w) w.val z)))
        w.val.val - (R.quotientAbsA x ^ 2 : ℝ) • ((starRingEnd ℂ) (G x) * H x) := by
  dsimp only
  rw [quotientJacobiDensity, R.assembleCopyDensity_ordered _ _ w hw]
  unfold copyJacobiDensity
  rw [R.oddCopy_inverseMetricPairing G H j.val w hw hw0]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [quotientAbsA, R.diskCoordinate_orderedDiskPoint,
    encodeDiskFunction_on_disk, encodeDiskFunction_on_disk]
  rfl

lemma quotientJacobiDensity_ae_geometry :
    ∀ᵐ x ∂(R.quotientArea),
      ∃ (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k),
        HeightLift.periodQuotientMap m q = x ∧
        (R.quotientJacobiDensity G H x =
          chartInvMetricGradInner (R.centeredChart q)
            (G ∘ (HeightLift.periodChart R.hC m x).symm)
            (H ∘ (HeightLift.periodChart R.hC m x).symm) w.val -
          (R.quotientAbsA x ^ 2 : ℝ) • ((starRingEnd ℂ) (G x) * H x) ∨
         R.quotientJacobiDensity G H x =
          chartInvMetricGradInner (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift q w)
            (fun z => G (HeightLift.periodQuotientMap m (R.lowerParameterLift q w z)))
            (fun z => H (HeightLift.periodQuotientMap m (R.lowerParameterLift q w z))) w.val -
          (R.quotientAbsA x ^ 2 : ℝ) • ((starRingEnd ℂ) (G x) * H x)) := by
  filter_upwards [R.ae_quotient_interior_nonzero (m := m)] with x hx
  obtain ⟨n, w, hw, hw0, rfl⟩ := hx
  obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n
  · exact ⟨R.evenDiskPoint j.val w, w.val, (R.orderedDiskPoint_even j w).symm,
      Or.inl (R.quotientJacobiDensity_even_geometry G H j w hw)⟩
  · exact ⟨R.oddDiskPoint j.val w, w.val, (R.orderedDiskPoint_odd j w).symm,
      Or.inr (R.quotientJacobiDensity_odd_geometry G H j w hw hw0)⟩

end PaperHalfPeriodRealization
end KsIndex.KarcherData
