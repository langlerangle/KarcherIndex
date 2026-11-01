module

public import KsIndexLean.KarcherSeamImageMeasure

@[expose] public section


/-! Actual upper-seam inverse charts transport the area determined by the
immersion's first fundamental form to the corresponding quotient-area piece. -/
noncomputable section
open Set MeasureTheory Topology
open scoped Topology KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
open scoped QuotientArea
namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

lemma upperSeam_immersionArea_transport (j : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : q ∈ R.upperSeamBand j) (hp : HeightLift.projection q = finiteParameter w) :
    ∃ r > 0,
      Metric.ball w.val r ⊆
        (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).target ∧
      Measure.map (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm
        ((immersionAreaMeasure (R.centeredChart q)).restrict (Metric.ball w.val r)) =
      ((R.quotientArea).restrict
        (R.quotientCopyInterior (evenCopyIndex (j : ZMod m)) ∪
          R.quotientCopyInterior (evenCopyIndex (j : ZMod m) + 1))).restrict
        (R.seamPairCoordinate (evenCopyIndex (j : ZMod m)) ⁻¹' Metric.ball w.val r) := by
  let q₀ := HeightLift.periodQuotientMap m q
  let e := HeightLift.periodChart R.hC m q₀
  have hec : e q₀ = w.val := by
    rw [HeightLift.periodChart_apply]
    change chartAt ℂ (HeightLift.projection q) (HeightLift.projection q) = _
    rw [hp, ParameterAtlas.parameter_chartAt_finite]
  have ht : w.val ∈ e.target := hec ▸ e.map_source (HeightLift.periodChart_mem R.hC m q₀)
  have hi := R.upperSeam_pair_inverse_germ (m := m) j q w hq hp
  have hd := R.centeredChart_finite_areaDensity_field q w hp
  have htarget : ∀ᶠ z in 𝓝 w.val, z ∈ e.target := e.open_target.mem_nhds ht
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp
    (hi.and (htarget.and hd))
  have hsub : Metric.ball w.val r ⊆ e.target := fun z hz => (hb z hz).2.1
  refine ⟨r, hr, hsub, ?_⟩
  rw [immersionAreaMeasure_restrict_eq measurableSet_ball (fun z hz => (hb z hz).2.2)]
  apply R.map_seam_inverse_restrict (copyIndex_ne_successor _) measurableSet_ball
  · exact (e.continuousOn_symm.mono hsub).aemeasurable measurableSet_ball
  · intro z hz
    exact (hb z hz).1

/-- The area measure induced by the actual immersion in an upper-seam chart
pushes forward to quotient area on the full open chart neighborhood. -/
lemma upperSeam_immersionArea_chart (j : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : q ∈ R.upperSeamBand j) (hp : HeightLift.projection q = finiteParameter w) :
    ∃ r > 0,
      let e := HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)
      Metric.ball w.val r ⊆ e.target ∧ IsOpen (e.symm '' Metric.ball w.val r) ∧
      Measure.map e.symm ((immersionAreaMeasure (R.centeredChart q)).restrict (Metric.ball w.val r)) =
        (R.quotientArea).restrict (e.symm '' Metric.ball w.val r) := by
  let q₀ := HeightLift.periodQuotientMap m q
  let e := HeightLift.periodChart R.hC m q₀
  have hec : e q₀ = w.val := by
    rw [HeightLift.periodChart_apply]
    change chartAt ℂ (HeightLift.projection q) (HeightLift.projection q) = _
    rw [hp, ParameterAtlas.parameter_chartAt_finite]
  have ht : w.val ∈ e.target := hec ▸ e.map_source (HeightLift.periodChart_mem R.hC m q₀)
  have hi := R.upperSeam_pair_inverse_germ (m := m) j q w hq hp
  have hd := R.centeredChart_finite_areaDensity_field q w hp
  have htarget : ∀ᶠ z in 𝓝 w.val, z ∈ e.target := e.open_target.mem_nhds ht
  have hs := R.upperSeam_closedPair_germ (m := m) j q w hq hp
  have hc := R.upperSeam_pairCoordinate_germ (m := m) j q w hq hp
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp
    (hi.and (htarget.and (hd.and (hs.and hc))))
  have hsub : Metric.ball w.val r ⊆ e.target := fun z hz => (hb z hz).2.1
  refine ⟨r, hr, hsub, e.symm.isOpen_image_of_subset_source Metric.isOpen_ball hsub, ?_⟩
  rw [immersionAreaMeasure_restrict_eq measurableSet_ball (fun z hz => (hb z hz).2.2.1)]
  calc
    _ = ((R.quotientArea).restrict
        (R.quotientCopyInterior (evenCopyIndex (j : ZMod m)) ∪
          R.quotientCopyInterior (evenCopyIndex (j : ZMod m) + 1))).restrict
        (R.seamPairCoordinate (evenCopyIndex (j : ZMod m)) ⁻¹' Metric.ball w.val r) := by
      apply R.map_seam_inverse_restrict (copyIndex_ne_successor _) measurableSet_ball
      · exact (e.continuousOn_symm.mono hsub).aemeasurable measurableSet_ball
      · intro z hz
        exact (hb z hz).1
    _ = _ := R.restrict_pair_preimage_eq_image _ measurableSet_ball e.symm
      (fun z hz => (hb z hz).2.2.2.1) (fun z hz => (hb z hz).2.2.2.2)
      (fun z hz => (hb z hz).1)

end PaperHalfPeriodRealization
end KsIndex.KarcherData
