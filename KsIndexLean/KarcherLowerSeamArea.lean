module

public import KsIndexLean.KarcherReflectedChartArea

@[expose] public section


/-! Induced area transport through the actual reflected lower-seam lift. -/
noncomputable section
open Set MeasureTheory Topology
open scoped Topology KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
open scoped QuotientArea
/-- Circle inversion maps open sets avoiding zero to open sets. -/
lemma isOpen_sigma_image {U : Set ℂ} (hU : IsOpen U) (hzero : ∀ z ∈ U, z ≠ 0) :
    IsOpen (Bracket.σ '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  have hx0 := hzero x hx
  have hs0 : Bracket.σ x ≠ 0 := by simpa [Bracket.σ] using hx0
  have ht : Bracket.σ ⁻¹' U ∈ 𝓝 (Bracket.σ x) :=
    (Bracket.continuousAt_σ hs0).preimage_mem_nhds (by
      simpa only [Bracket.σ_σ] using hU.mem_nhds hx)
  exact Filter.mem_of_superset ht (fun z hz => ⟨Bracket.σ z, hz, Bracket.σ_σ z⟩)

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

/-- The lower-seam immersion measure transports to quotient area on the entire
image of a sufficiently small coordinate ball, including the seam itself. -/
lemma lowerSeam_immersionArea_chart (j : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hw : w.val ≠ 0) (hq : q ∈ R.lowerSeamBand j)
    (hp : parameterSeamReflection h.out (HeightLift.projection q) = finiteParameter w) :
    ∃ r > 0,
      let g := HeightLift.periodQuotientMap m ∘ R.lowerParameterLift q w
      IsOpen (g '' Metric.ball w.val r) ∧
      HeightLift.periodQuotientMap m q ∈ g '' Metric.ball w.val r ∧
      Set.InjOn g (Metric.ball w.val r) ∧
      ContinuousOn g (Metric.ball w.val r) ∧
      Measure.map g
        ((immersionAreaMeasure (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift q w)).restrict
          (Metric.ball w.val r)) =
        (R.quotientArea).restrict (g '' Metric.ball w.val r) := by
  let v : PuncturedPlane k := ⟨((starRingEnd ℂ) w.val)⁻¹,
    inverse_conjugate_not_puncture w.property⟩
  have hv : v.val = Bracket.σ w.val := by simp [v, Bracket.σ]
  have hproj : HeightLift.projection q = finiteParameter v := by
    have hs : parameterSeamReflection h.out (finiteParameter w) = HeightLift.projection q := by
      rw [← hp, parameterSeamReflection_involutive]
    rw [← hs]
    exact parameterSeamReflection_finite h.out w hw (inverse_conjugate_not_puncture w.property)
  let g := HeightLift.periodQuotientMap m ∘ R.lowerParameterLift q w
  have hi := R.lowerSeam_pair_inverse_germ (m := m) j q w hq hp
  have hd := R.lowerParameterLift_areaDensity_field q w v hw hv hproj
  have ht := R.lowerParameterLift_continuousAt_field q w v hw hv hproj
  have hs := R.lowerSeam_closedPair_germ (m := m) j q w hq hp
  have hc := R.lowerSeam_pairCoordinate_germ (m := m) j q w hq hp
  let e := HeightLift.liftChart R.hC q
  have het : Bracket.σ w.val ∈ e.target := by
    rw [← hv, ← R.chartCenter_finite q v hproj]
    exact e.map_source (HeightLift.liftChart_mem R.hC q)
  have htar : ∀ᶠ z in 𝓝 (Bracket.σ w.val), z ∈ e.target := e.open_target.mem_nhds het
  have hzero : ∀ᶠ z in 𝓝 w.val, z ≠ 0 :=
    isOpen_ne_fun continuous_id continuous_const |>.mem_nhds hw
  have hextra := (R.lowerParameterLift_finite_germ q w v hw hv hproj).and
    (((Bracket.continuousAt_σ hw).tendsto.eventually htar).and hzero)
  obtain ⟨r, hr, hbAll⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hi.and (ht.and (hd.and (hs.and hc)))).and hextra)
  have hb := fun z hz => (hbAll z hz).1
  have hext := fun z hz => (hbAll z hz).2
  have hcont : ContinuousOn g (Metric.ball w.val r) := by
    intro z hz
    exact ((HeightLift.periodQuotientMap_isQuotientMap m).continuous.continuousAt.comp
      (hb z hz).2.1).continuousWithinAt
  have hopen : IsOpen (g '' Metric.ball w.val r) := by
    have hsopen := isOpen_sigma_image Metric.isOpen_ball (fun z hz => (hext z hz).2.2)
    have hsub : Bracket.σ '' Metric.ball w.val r ⊆ e.target := by
      rintro y ⟨z, hz, rfl⟩
      exact (hext z hz).2.1
    have hopen := (HeightLift.periodQuotientMap_isLocalHomeomorph R.hC m).isOpenMap _
      (e.symm.isOpen_image_of_subset_source hsopen hsub)
    have heq : g '' Metric.ball w.val r =
        HeightLift.periodQuotientMap m '' (e.symm '' (Bracket.σ '' Metric.ball w.val r)) := by
      rw [← Set.image_comp, ← Set.image_comp]
      apply Set.image_congr
      intro z hz
      exact congrArg (HeightLift.periodQuotientMap m) (hext z hz).1
    rw [heq]
    exact hopen
  have hcenter : HeightLift.periodQuotientMap m q ∈ g '' Metric.ball w.val r := by
    refine ⟨w.val, Metric.mem_ball_self hr, ?_⟩
    change HeightLift.periodQuotientMap m (R.lowerParameterLift q w w.val) = _
    rw [(hext w.val (Metric.mem_ball_self hr)).1]
    change HeightLift.periodQuotientMap m (e.symm (Bracket.σ w.val)) = _
    have hec : e q = Bracket.σ w.val := by
      exact (R.chartCenter_finite q v hproj).trans hv
    rw [← hec, e.left_inv (HeightLift.liftChart_mem R.hC q)]
  have hinj : Set.InjOn g (Metric.ball w.val r) := by
    intro a ha b hb' hab
    have hc := congrArg (R.seamPairCoordinate (oddCopyIndex (j : ZMod m))) hab
    exact ((hb a ha).2.2.2.2).symm.trans (hc.trans (hb b hb').2.2.2.2)
  refine ⟨r, hr, hopen, hcenter, hinj, hcont, ?_⟩
  rw [immersionAreaMeasure_restrict_eq measurableSet_ball (fun z hz => (hb z hz).2.2.1)]
  calc
    _ = ((R.quotientArea).restrict
        (R.quotientCopyInterior (oddCopyIndex (j : ZMod m)) ∪
          R.quotientCopyInterior (oddCopyIndex (j : ZMod m) + 1))).restrict
        (R.seamPairCoordinate (oddCopyIndex (j : ZMod m)) ⁻¹' Metric.ball w.val r) := by
      apply R.map_seam_inverse_restrict (copyIndex_ne_successor _) measurableSet_ball
      · exact hcont.aemeasurable measurableSet_ball
      · intro z hz
        exact (hb z hz).1
    _ = _ := R.restrict_pair_preimage_eq_image _ measurableSet_ball g
      (fun z hz => (hb z hz).2.2.2.1) (fun z hz => (hb z hz).2.2.2.2)
      (fun z hz => (hb z hz).1)

end PaperHalfPeriodRealization
end KsIndex.KarcherData
