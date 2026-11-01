module

public import KsIndexLean.KarcherInteriorAreaTransport

@[expose] public section


/-! Full induced-area neighborhoods in the actual infinity charts. -/
noncomputable section
open Set MeasureTheory Topology
open scoped Topology KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
open scoped QuotientArea
namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

lemma periodChart_infinity_on_odd (j : ZMod m)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hp : HeightLift.projection q = infinityParameter k)
    (x : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m)
    (hx : x ∈ R.quotientCopyInterior (oddCopyIndex j)) :
    HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q) x =
      (starRingEnd ℂ) (R.diskCoordinate x).val.val := by
  obtain ⟨w, hw, rfl⟩ := hx
  rw [R.diskCoordinate_orderedDiskPoint, R.orderedDiskPoint_odd,
    HeightLift.periodChart_apply]
  change chartAt ℂ (HeightLift.projection q)
    (HeightLift.projection (R.oddDiskPoint j.val w)) = _
  rw [hp, R.oddDiskPoint_projection]
  exact infinity_coordinate_reflected w.val

lemma infinity_localInducedAreaLaw (j : ZMod m) (w : PuncturedClosedDisk k)
    (hw : w.val.val = 0) :
    LocalInducedAreaLaw R.quotientArea (R.centeredChart (R.oddDiskPoint j.val w))
      (HeightLift.periodChart R.hC m (R.oddPeriodPoint m j.val w)).symm
      0 (R.oddPeriodPoint m j.val w) := by
  let q := R.oddDiskPoint j.val w
  let x := R.oddPeriodPoint m j.val w
  let e := HeightLift.periodChart R.hC m x
  let C := fun y => (starRingEnd ℂ) (R.diskCoordinate (m := m) y).val.val
  have hw' : w.val = (⟨0, zero_not_puncture h.out⟩ : PuncturedPlane k) := Subtype.ext hw
  have hp : HeightLift.projection q = infinityParameter k := by
    rw [R.oddDiskPoint_projection, hw', parameterSeamReflection_zero]
  have hx : x ∈ R.quotientCopyInterior (oddCopyIndex j) := by
    refine ⟨w, by simp [hw], ?_⟩
    exact R.orderedDiskPoint_odd j w
  have hec : e x = 0 := by
    change HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q) x = 0
    rw [R.periodChart_infinity_on_odd j q hp x hx]
    change C x = 0
    have hh : x = R.orderedDiskPoint (oddCopyIndex j) w := (R.orderedDiskPoint_odd j w).symm
    simp only [C, hh, R.diskCoordinate_orderedDiskPoint, hw, map_zero]
  have ht : (0 : ℂ) ∈ e.target := hec ▸ e.map_source (HeightLift.periodChart_mem R.hC m x)
  have he0 : e.symm 0 = x := by
    rw [← hec]
    exact e.left_inv (HeightLift.periodChart_mem R.hC m x)
  have htar : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ e.target := e.open_target.mem_nhds ht
  have hsupport : ∀ᶠ z in 𝓝 (0 : ℂ), e.symm z ∈ R.quotientCopyInterior (oddCopyIndex j) := by
    apply (e.continuousAt_symm ht).preimage_mem_nhds
    rw [he0]
    exact (R.isOpen_quotientCopyInterior _).mem_nhds hx
  have hd := R.centeredChart_infinity_areaDensity_field q hp
  have hdi : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ Surface.disk := Metric.isOpen_ball.mem_nhds (by simp)
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp (htar.and (hsupport.and (hd.and hdi)))
  have hsub : Metric.ball (0 : ℂ) r ⊆ e.target := fun z hz => (hb z hz).1
  refine ⟨r, hr, e.symm.isOpen_image_of_subset_source Metric.isOpen_ball hsub,
    ⟨0, Metric.mem_ball_self hr, he0⟩, e.symm.injOn.mono hsub, e.continuousOn_symm.mono hsub, ?_⟩
  rw [immersionAreaMeasure_restrict_eq measurableSet_ball (fun z hz => (hb z hz).2.2.1)]
  apply R.map_copy_inverse_area (oddCopyIndex j) C
    (Complex.continuous_conj.measurable.comp R.continuous_diskCoordinate_val.measurable)
    (fun a ha b hb hab => R.diskCoordinate_val_injOn_copy _ ha hb
      ((starRingEnd ℂ).injective hab)) measurableSet_ball (fun z hz => (hb z hz).2.2.2)
    (R.map_conj_diskCoordinate_area_restrict _) e.symm
    ((e.continuousOn_symm.mono hsub).aemeasurable measurableSet_ball)
    (fun z hz => (hb z hz).2.1)
  intro z hz
  change (starRingEnd ℂ) (R.diskCoordinate (e.symm z)).val.val = z
  rw [← R.periodChart_infinity_on_odd j q hp (e.symm z) (hb z hz).2.1]
  exact e.right_inv (hsub hz)

end PaperHalfPeriodRealization
end KsIndex.KarcherData
