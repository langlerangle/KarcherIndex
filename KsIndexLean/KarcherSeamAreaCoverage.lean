module

public import KsIndexLean.KarcherLowerSeamArea

@[expose] public section


/-! Local induced-area laws at every actual circle seam, including the cyclic
junction. The alternatives retain the actual upper and reflected lower lifts. -/
noncomputable section
open Set MeasureTheory Topology
open scoped Topology KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
open scoped QuotientArea

/-- A parametrization transports its immersion's induced area to a full open
neighborhood of the specified point. -/
def LocalInducedAreaLaw {Q : Type*} [TopologicalSpace Q] [MeasurableSpace Q]
    (μ : Measure Q) (X : ℂ → AmbientTriple) (g : ℂ → Q) (z : ℂ) (q : Q) : Prop :=
  ∃ r > 0, IsOpen (g '' Metric.ball z r) ∧ q ∈ g '' Metric.ball z r ∧
    Set.InjOn g (Metric.ball z r) ∧ ContinuousOn g (Metric.ball z r) ∧
    Measure.map g ((immersionAreaMeasure X).restrict (Metric.ball z r)) =
      μ.restrict (g '' Metric.ball z r)

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

lemma upperSeam_localInducedAreaLaw (j : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : q ∈ R.upperSeamBand j) (hp : HeightLift.projection q = finiteParameter w) :
    LocalInducedAreaLaw R.quotientArea (R.centeredChart q)
      (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm
      w.val (HeightLift.periodQuotientMap m q) := by
  obtain ⟨r, hr, hsub, ho, hm⟩ := R.upperSeam_immersionArea_chart (m := m) j q w hq hp
  let q₀ := HeightLift.periodQuotientMap m q
  let e := HeightLift.periodChart R.hC m q₀
  have hec : e q₀ = w.val := by
    rw [HeightLift.periodChart_apply]
    change chartAt ℂ (HeightLift.projection q) (HeightLift.projection q) = _
    rw [hp, ParameterAtlas.parameter_chartAt_finite]
  refine ⟨r, hr, ho, ?_, e.symm.injOn.mono hsub, e.continuousOn_symm.mono hsub, hm⟩
  refine ⟨w.val, Metric.mem_ball_self hr, ?_⟩
  rw [← hec]
  exact e.left_inv (HeightLift.periodChart_mem R.hC m q₀)

lemma lowerSeam_localInducedAreaLaw (j : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hw : w.val ≠ 0) (hq : q ∈ R.lowerSeamBand j)
    (hp : parameterSeamReflection h.out (HeightLift.projection q) = finiteParameter w) :
    LocalInducedAreaLaw R.quotientArea
      (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift q w)
      (HeightLift.periodQuotientMap m ∘ R.lowerParameterLift q w)
      w.val (HeightLift.periodQuotientMap m q) :=
  R.lowerSeam_immersionArea_chart j q w hw hq hp

/-- Every actual circle point has an induced-area neighborhood of one of the
 two seam types. The band cover uses integer heights, so this also covers the
 quotient's wraparound seam and the two-copy case. -/
lemma circle_localInducedAreaLaw
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hw : ‖w.val‖ = 1) (hp : HeightLift.projection q = finiteParameter w) :
    LocalInducedAreaLaw R.quotientArea (R.centeredChart q)
      (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm
      w.val (HeightLift.periodQuotientMap m q) ∨
    LocalInducedAreaLaw R.quotientArea
      (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift q w)
      (HeightLift.periodQuotientMap m ∘ R.lowerParameterLift q w)
      w.val (HeightLift.periodQuotientMap m q) := by
  have hw0 : w.val ≠ 0 := by intro hz; simp [hz] at hw
  obtain ⟨j, hu | hl⟩ := R.seamBands_cover q
  · exact Or.inl (R.upperSeam_localInducedAreaLaw j q w hu hp)
  · apply Or.inr
    apply R.lowerSeam_localInducedAreaLaw j q w hw0 hl
    rw [hp, parameterSeamReflection_finite h.out w hw0
      (inverse_conjugate_not_puncture w.property)]
    congr 1
    apply Subtype.ext
    simpa only [Bracket.σ, one_div] using Bracket.σ_self hw

/-- Quotient seams have actual finite circle representatives. -/
lemma quotientSeam_circle_lift
    (x : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m)
    (hx : x ∈ R.quotientSeams) :
    ∃ q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C, ∃ w : PuncturedPlane k,
      HeightLift.periodQuotientMap m q = x ∧ ‖w.val‖ = 1 ∧
      HeightLift.projection q = finiteParameter w := by
  obtain ⟨n, w, hw, rfl⟩ := hx
  obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n
  · exact ⟨R.evenDiskPoint j.val w, w.val,
      (R.orderedDiskPoint_even j w).symm, hw, R.evenDiskPoint_projection j.val w⟩
  · refine ⟨R.oddDiskPoint j.val w, w.val,
      (R.orderedDiskPoint_odd j w).symm, hw, ?_⟩
    rw [R.oddDiskPoint_projection]
    have hw0 : w.val.val ≠ 0 := by intro hz; simp [hz] at hw
    rw [parameterSeamReflection_finite h.out w.val hw0
      (inverse_conjugate_not_puncture w.val.property)]
    congr 1
    apply Subtype.ext
    simpa only [Bracket.σ, one_div] using Bracket.σ_self hw

/-- Every point of the actual quotient seam set has a full induced-area
neighborhood. The immersion is one of the two explicitly constructed lifts. -/
lemma quotientSeam_localInducedAreaLaw
    (x : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m)
    (hx : x ∈ R.quotientSeams) :
    ∃ (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k),
      HeightLift.periodQuotientMap m q = x ∧ ‖w.val‖ = 1 ∧
      HeightLift.projection q = finiteParameter w ∧
      (LocalInducedAreaLaw R.quotientArea (R.centeredChart q)
        (HeightLift.periodChart R.hC m x).symm w.val x ∨
       LocalInducedAreaLaw R.quotientArea
        (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift q w)
        (HeightLift.periodQuotientMap m ∘ R.lowerParameterLift q w) w.val x) := by
  obtain ⟨q, w, hqx, hw, hp⟩ := R.quotientSeam_circle_lift x hx
  refine ⟨q, w, hqx, hw, hp, ?_⟩
  simpa only [hqx] using R.circle_localInducedAreaLaw (m := m) q w hw hp

end PaperHalfPeriodRealization
end KsIndex.KarcherData
