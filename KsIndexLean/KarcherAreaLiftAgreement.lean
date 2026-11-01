module

public import KsIndexLean.KarcherQuotientPairingGeometry

@[expose] public section


/-! Agreement between the quotient chart used for scalar functions and the
lifted chart used for the ambient immersion and its first fundamental form. -/
noncomputable section
open Set Topology
open scoped Topology KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
namespace HeightLift
variable {P : Type*} [TopologicalSpace P] [ChartedSpace ℂ P]
variable {F : P → PeriodTarget}

lemma periodChart_symm_lift_germ (hF : Continuous F) (m : ℕ) (q : HeightLift F) :
    (periodQuotientMap m ∘ (liftChart hF q).symm) =ᶠ[
      𝓝 (chartAt ℂ (projection q) (projection q))]
      (periodChart hF m (periodQuotientMap m q)).symm := by
  let b := chartAt ℂ (projection q)
  have ht : b (projection q) ∈ b.target := b.map_source (mem_chart_source ℂ (projection q))
  have hi : b.symm (b (projection q)) = projection q := b.left_inv (mem_chart_source ℂ (projection q))
  have hc := (b.continuousAt_symm ht).tendsto
  rw [hi] at hc
  have hg := (localInverse_periodQuotient_germ hF m q).comp_tendsto hc
  exact hg

end HeightLift
namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

omit [NeZero m] in
/-- The scalar pullback in the quotient chart uses precisely the lift whose
ambient immersion is `centeredChart`, as a germ at the chart center. -/
lemma centeredChart_scalar_pullback_germ
    (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    (G ∘ HeightLift.periodQuotientMap m ∘ (HeightLift.liftChart R.hC q).symm) =ᶠ[𝓝 (R.chartCenter q)]
      (G ∘ (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm) := by
  have hg := HeightLift.periodChart_symm_lift_germ R.hC m q
  rw [chartCenter, HeightLift.liftChart_apply]
  filter_upwards [hg] with z hz
  exact congrArg G hz

end PaperHalfPeriodRealization
end KsIndex.KarcherData
