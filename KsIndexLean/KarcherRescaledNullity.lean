module

public import KsIndexLean.KarcherHomothetyJacobi
public import KsIndexLean.KarcherRescaledAmbient
public import KsIndexLean.KarcherPeriodicNullity

@[expose] public section


/-! The rescaled normalized EW quotient in the fixed ambient period, and its Jacobi fields. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

/-- Normalize as in the paper, then scale by 1/m into the fixed 2π ambient quotient. -/
def rescaledNormalizedPeriodMap
    (x : HeightLift.PeriodQuotient
        (extendedEWMap h.out (reflectionBasepoint k) R.C) m) : PeriodTarget :=
  projectPeriod ((m : ℝ)⁻¹ • ((R.t,0,Real.pi) : AmbientTriple)) +
    HeightLift.rescaledPeriodMap m x

lemma rescaledNormalizedPeriodMap_local
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    (R.rescaledNormalizedPeriodMap ∘ (HeightLift.periodChart R.hC m
      (HeightLift.periodQuotientMap m q)).symm) =ᶠ[𝓝 (R.chartCenter q)]
      (projectPeriod ∘ ((m : ℝ)⁻¹ • R.centeredChart q)) := by
  have he := HeightLift.periodChart_symm_lift_germ R.hC m q
  change _ =ᶠ[𝓝 (HeightLift.liftChart R.hC q q)] _
  rw [HeightLift.liftChart_apply]
  filter_upwards [he] with z hz
  change R.rescaledNormalizedPeriodMap ((HeightLift.periodChart R.hC m
    (HeightLift.periodQuotientMap m q)).symm z) = _
  rw [← hz]
  simp only [rescaledNormalizedPeriodMap, HeightLift.rescaledPeriodMap_mk,
    HeightLift.rescaledAmbient, R.centeredChart_eq_translate, Pi.smul_apply,
    Function.comp_apply, smul_add, projectPeriod_add]

lemma continuous_rescaledNormalizedPeriodMap :
    Continuous (R.rescaledNormalizedPeriodMap (m := m)) :=
  continuous_const.add (HeightLift.continuous_rescaledPeriodMap m R.hC)

/-- Operator computed from the actual scaled local immersion representative. -/
def rescaledJacobiAt
    (g : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) : ℂ :=
  chartJacobiOperator ((m : ℝ)⁻¹ • R.centeredChart q)
    (g ∘ (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm)
    (R.chartCenter q)

lemma rescaledJacobiAt_eq
    (g : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.rescaledJacobiAt g q = (((m : ℝ)⁻¹ ^ 2)⁻¹ : ℝ) * R.geometricJacobiAt g q := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have ht : R.chartCenter q ∈ (HeightLift.liftChart R.hC q).target :=
    (HeightLift.liftChart R.hC q).map_source (HeightLift.liftChart_mem R.hC q)
  have hn : ∀ᶠ z in 𝓝 (R.chartCenter q), DifferentiableAt ℝ (R.centeredChart q) z := by
    filter_upwards [(HeightLift.liftChart R.hC q).open_target.mem_nhds ht] with z hz
    exact (R.centeredChart_contDiffAt q hz).differentiableAt (by simp)
  have hc : HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)
      (HeightLift.periodQuotientMap m q) = R.chartCenter q := by
    simp only [HeightLift.periodChart_apply, chartCenter, HeightLift.liftChart_apply]
    rfl
  have hi := (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).left_inv
    (HeightLift.periodChart_mem R.hC m (HeightLift.periodQuotientMap m q))
  rw [hc] at hi
  simpa only [rescaledJacobiAt, geometricJacobiAt, chartJacobiOperator, Function.comp_apply,
    hi] using
    chartJacobiOperator_homothety ((R.centeredChart_contDiffAt q ht).of_le (by simp))
      hn (inv_ne_zero hm)
      (g ∘ (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm)

/-- Bounded smooth Jacobi fields of the scaled fixed-ambient immersion. -/
def IsBoundedRescaledJacobi
    (g : HeightLift.PeriodQuotient
        (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) : Prop :=
  letI := HeightLift.periodChartedSpace R.hC m
  ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g ∧ (∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) ∧
    ∀ q, R.rescaledJacobiAt g q = 0

lemma boundedRescaledJacobi_iff
    (g : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    R.IsBoundedRescaledJacobi g ↔ R.IsBoundedGeometricJacobi g := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hc : ((((m : ℝ)⁻¹ ^ 2)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero (pow_ne_zero 2 (inv_ne_zero hm))
  change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  simp only [rescaledJacobiAt_eq, mul_eq_zero, hc, false_or, IsGeometricJacobi]

/-- The vector space specified by the actual rescaled Jacobi equation. -/
def boundedRescaledJacobi : Submodule ℂ
    (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) where
  carrier := {g | R.IsBoundedRescaledJacobi g}
  zero_mem' := (R.boundedRescaledJacobi_iff 0).mpr R.isBoundedGeometricJacobi_zero
  add_mem' := by
    intro f g hf hg
    exact (R.boundedRescaledJacobi_iff (f+g)).mpr
      (IsBoundedGeometricJacobi.add R ((R.boundedRescaledJacobi_iff f).mp hf)
        ((R.boundedRescaledJacobi_iff g).mp hg))
  smul_mem' := by
    intro c f hf
    exact (R.boundedRescaledJacobi_iff (c • f)).mpr
      (IsBoundedGeometricJacobi.smul R c ((R.boundedRescaledJacobi_iff f).mp hf))

lemma boundedRescaledJacobi_eq : R.boundedRescaledJacobi (m := m) = R.boundedGeometricJacobi := by
  ext g
  exact R.boundedRescaledJacobi_iff g

def rescaledNullity : ℕ∞ := Cardinal.toENat (Module.rank ℂ (R.boundedRescaledJacobi (m := m)))

lemma rescaledNullity_eq_geometricNullity :
    R.rescaledNullity (m := m) = R.geometricNullity (m := m) := by
  unfold rescaledNullity geometricNullity
  rw [R.boundedRescaledJacobi_eq]

lemma rescaledNullity_eq_model : R.rescaledNullity (m := m) = Surface.nulSurface k m := by
  rw [R.rescaledNullity_eq_geometricNullity, R.geometricNullity_eq_model]

end KsIndex.KarcherData.PaperHalfPeriodRealization
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.rescaledNormalizedPeriodMap_local
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.rescaledJacobiAt_eq
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.rescaledNullity_eq_model
