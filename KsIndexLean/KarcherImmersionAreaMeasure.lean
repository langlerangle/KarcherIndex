module

public import KsIndexLean.KarcherChartMetricField
public import KsIndexLean.KarcherAreaInversion
public import KsIndexLean.KarcherQuotientAreaCoordinates

@[expose] public section


/-! Local area measures defined from the actual immersion's Gram matrix.
Their identification with the EW coordinate measure is proved on neighborhoods,
including the chart centered at infinity. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace KsIndex.KarcherData

/-- Coordinate area determined by the first fundamental form of an immersion. -/
def immersionAreaMeasure (X : ℂ → AmbientTriple) : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (chartAreaDensity X z))

lemma immersionAreaMeasure_restrict_eq {k : ℕ} {X : ℂ → AmbientTriple}
    {U : Set ℂ} (hU : MeasurableSet U)
    (hX : ∀ z ∈ U, chartAreaDensity X z = Surface.rho k z ^ 2) :
    (immersionAreaMeasure X).restrict U = (ewAreaMeasure k).restrict U := by
  rw [immersionAreaMeasure, ewAreaMeasure,
    restrict_withDensity hU, restrict_withDensity hU]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hU] with z hz
  rw [hX z hz]

lemma exists_ball_immersionAreaMeasure_eq {k : ℕ} {X : ℂ → AmbientTriple} {w : ℂ}
    (hX : (fun z => chartAreaDensity X z) =ᶠ[𝓝 w] (fun z => Surface.rho k z ^ 2)) :
    ∃ r > 0, (immersionAreaMeasure X).restrict (Metric.ball w r) =
      (ewAreaMeasure k).restrict (Metric.ball w r) := by
  obtain ⟨r, hr, he⟩ := Metric.eventually_nhds_iff_ball.mp hX
  exact ⟨r, hr, immersionAreaMeasure_restrict_eq measurableSet_ball he⟩

open scoped QuotientArea
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

/-- The actual finite chart's induced area agrees with EW area on a neighborhood.
There is no restriction to points lying strictly inside a disk copy. -/
lemma centeredChart_finite_areaMeasure
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) :
    ∃ r > 0, (immersionAreaMeasure (R.centeredChart q)).restrict (Metric.ball w.val r) =
      (ewAreaMeasure k).restrict (Metric.ball w.val r) :=
  exists_ball_immersionAreaMeasure_eq (R.centeredChart_finite_areaDensity_field q w hq)

/-- The actual infinity chart's induced area uses the same EW density near zero. -/
lemma centeredChart_infinity_areaMeasure
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = infinityParameter k) :
    ∃ r > 0, (immersionAreaMeasure (R.centeredChart q)).restrict (Metric.ball 0 r) =
      (ewAreaMeasure k).restrict (Metric.ball 0 r) :=
  exists_ball_immersionAreaMeasure_eq (R.centeredChart_infinity_areaDensity_field q hq)

/-- On an even disk interior, the quotient area really is the actual centered
immersion's area measure in finite coordinates, on a neighborhood of the point. -/
lemma quotientArea_even_local {m : ℕ} [NeZero m] (j : ZMod m)
    (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ < 1) :
    ∃ r > 0, Measure.map (fun q => (R.diskCoordinate q).val.val)
      (((R.quotientArea).restrict (R.quotientCopyInterior (evenCopyIndex j))).restrict
        ((fun q => (R.diskCoordinate q).val.val) ⁻¹' Metric.ball w.val.val r)) =
      (immersionAreaMeasure (R.centeredChart (R.evenDiskPoint j.val w))).restrict
        (Metric.ball w.val.val r) := by
  have hd := R.centeredChart_finite_areaDensity_field (R.evenDiskPoint j.val w) w.val
    (R.evenDiskPoint_projection j.val w)
  have hi : ∀ᶠ z in 𝓝 w.val.val, z ∈ Surface.disk :=
    Metric.isOpen_ball.mem_nhds (SurfaceForm.mem_disk_iff.mpr hw)
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp (hd.and hi)
  refine ⟨r, hr, ?_⟩
  rw [← Measure.restrict_map R.continuous_diskCoordinate_val.measurable measurableSet_ball,
    R.map_diskCoordinate_area_restrict]
  rw [Measure.restrict_restrict measurableSet_ball]
  have hs : Metric.ball w.val.val r ∩ Surface.disk = Metric.ball w.val.val r :=
    Set.inter_eq_left.mpr (fun z hz => (hb z hz).2)
  rw [hs]
  exact (immersionAreaMeasure_restrict_eq measurableSet_ball (fun z hz => (hb z hz).1)).symm

/-- Reflected disk coordinates express a copy's area as EW area on the exterior. -/
lemma map_sigma_diskCoordinate_area_restrict {m : ℕ} [NeZero m] (n : ZMod (2*m)) :
    Measure.map (fun q => Bracket.σ (R.diskCoordinate q).val.val)
      ((R.quotientArea).restrict (R.quotientCopyInterior n)) =
      (ewAreaMeasure k).restrict {z : ℂ | 1 < ‖z‖} := by
  rw [show (fun q => Bracket.σ (R.diskCoordinate q).val.val) =
    Bracket.σ ∘ (fun q => (R.diskCoordinate q).val.val) from rfl,
    ← Measure.map_map Spherical.measurable_sigma R.continuous_diskCoordinate_val.measurable,
    R.map_diskCoordinate_area_restrict, map_ewAreaMeasure_sigma_disk h.out]

/-- Away from its center, an odd disk copy has the actual finite-coordinate
area measure after circle inversion. The center itself uses the infinity chart. -/
lemma quotientArea_odd_local {m : ℕ} [NeZero m] (j : ZMod m)
    (w : PuncturedClosedDisk k) (hw : ‖w.val.val‖ < 1) (hw0 : w.val.val ≠ 0) :
    ∃ r > 0, Measure.map (fun q => Bracket.σ (R.diskCoordinate q).val.val)
      (((R.quotientArea).restrict (R.quotientCopyInterior (oddCopyIndex j))).restrict
        ((fun q => Bracket.σ (R.diskCoordinate q).val.val) ⁻¹'
          Metric.ball (Bracket.σ w.val.val) r)) =
      (immersionAreaMeasure (R.centeredChart (R.oddDiskPoint j.val w))).restrict
        (Metric.ball (Bracket.σ w.val.val) r) := by
  let v : PuncturedPlane k :=
    ⟨(starRingEnd ℂ w.val.val)⁻¹, inverse_conjugate_not_puncture w.val.property⟩
  have hv : v.val = Bracket.σ w.val.val := by simp [v, Bracket.σ]
  have hp : HeightLift.projection (R.oddDiskPoint j.val w) = finiteParameter v := by
    rw [R.oddDiskPoint_projection]
    exact parameterSeamReflection_finite h.out w.val hw0 v.property
  have hd := R.centeredChart_finite_areaDensity_field (R.oddDiskPoint j.val w) v hp
  rw [hv] at hd
  have hi : ∀ᶠ z in 𝓝 (Bracket.σ w.val.val), 1 < ‖z‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds
      (lt_of_not_ge (Bracket.not_norm_σ_le hw0 hw))
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp (hd.and hi)
  refine ⟨r, hr, ?_⟩
  rw [← Measure.restrict_map (f := fun q => Bracket.σ (R.diskCoordinate q).val.val)
      (Spherical.measurable_sigma.comp R.continuous_diskCoordinate_val.measurable) measurableSet_ball,
    R.map_sigma_diskCoordinate_area_restrict, Measure.restrict_restrict measurableSet_ball]
  have hs : Metric.ball (Bracket.σ w.val.val) r ∩ {z : ℂ | 1 < ‖z‖} =
      Metric.ball (Bracket.σ w.val.val) r :=
    Set.inter_eq_left.mpr (fun z hz => (hb z hz).2)
  rw [hs]
  exact (immersionAreaMeasure_restrict_eq measurableSet_ball (fun z hz => (hb z hz).1)).symm

lemma map_conj_diskCoordinate_area_restrict {m : ℕ} [NeZero m] (n : ZMod (2*m)) :
    Measure.map (fun q => (starRingEnd ℂ) (R.diskCoordinate q).val.val)
      ((R.quotientArea).restrict (R.quotientCopyInterior n)) =
      (ewAreaMeasure k).restrict Surface.disk := by
  rw [show (fun q => (starRingEnd ℂ) (R.diskCoordinate q).val.val) =
    (starRingEnd ℂ) ∘ (fun q => (R.diskCoordinate q).val.val) from rfl,
    ← Measure.map_map Complex.continuous_conj.measurable R.continuous_diskCoordinate_val.measurable,
    R.map_diskCoordinate_area_restrict, map_ewAreaMeasure_conj_disk]

open scoped ParameterAtlas in
/-- The existing holomorphic infinity chart takes the reflected disk parameter
to its conjugate, including the disk center itself. -/
lemma infinity_coordinate_reflected (w : PuncturedPlane k) :
    chartAt ℂ (infinityParameter k) (parameterSeamReflection h.out (finiteParameter w)) =
      (starRingEnd ℂ) w.val := by
  change chartAt ℂ (infinitySphereChart 0) (Spherical.southChart w.val) = _
  rw [ParameterAtlas.sphere_chartAt_infinity]
  have he : Spherical.southChart w.val = infinitySphereChart ((starRingEnd ℂ) w.val) := by
    simp only [infinitySphereChart, Complex.conj_conj]
  rw [he, ParameterAtlas.infinity_apply]

/-- Quotient area agrees with the actual immersion's area in an infinity
chart on a whole neighborhood of every odd-copy center. -/
lemma quotientArea_infinity_local {m : ℕ} [NeZero m] (j : ZMod m)
    (w : PuncturedClosedDisk k) (hw : w.val.val = 0) :
    ∃ r > 0, Measure.map (fun q => (starRingEnd ℂ) (R.diskCoordinate q).val.val)
      (((R.quotientArea).restrict (R.quotientCopyInterior (oddCopyIndex j))).restrict
        ((fun q => (starRingEnd ℂ) (R.diskCoordinate q).val.val) ⁻¹' Metric.ball 0 r)) =
      (immersionAreaMeasure (R.centeredChart (R.oddDiskPoint j.val w))).restrict
        (Metric.ball 0 r) := by
  have hw' : w.val = (⟨0, zero_not_puncture h.out⟩ : PuncturedPlane k) := Subtype.ext hw
  have hp : HeightLift.projection (R.oddDiskPoint j.val w) = infinityParameter k := by
    rw [R.oddDiskPoint_projection, hw', parameterSeamReflection_zero]
  have hd := R.centeredChart_infinity_areaDensity_field (R.oddDiskPoint j.val w) hp
  have hi : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ Surface.disk :=
    Metric.isOpen_ball.mem_nhds (by simp)
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp (hd.and hi)
  refine ⟨r, hr, ?_⟩
  rw [← Measure.restrict_map (f := fun q => (starRingEnd ℂ) (R.diskCoordinate q).val.val)
      (Complex.continuous_conj.measurable.comp R.continuous_diskCoordinate_val.measurable)
      measurableSet_ball,
    R.map_conj_diskCoordinate_area_restrict, Measure.restrict_restrict measurableSet_ball]
  have hs : Metric.ball (0 : ℂ) r ∩ Surface.disk = Metric.ball 0 r :=
    Set.inter_eq_left.mpr (fun z hz => (hb z hz).2)
  rw [hs]
  exact (immersionAreaMeasure_restrict_eq measurableSet_ball (fun z hz => (hb z hz).1)).symm

end PaperHalfPeriodRealization
end KsIndex.KarcherData
