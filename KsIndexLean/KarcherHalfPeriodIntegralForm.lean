module

public import KsIndexLean.KarcherHalfPeriodArea
public import KsIndexLean.KarcherHalfPeriodChartForm
public import KsIndexLean.KarcherPolarizedForm

@[expose] public section


/-! The actual half-period area integral agrees with the immersion chart
integral and hence with the disk Jacobi form. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.KarcherData
open scoped QuotientArea HalfPeriodArea

lemma integral_ewAreaMeasure_disk_real (k : ℕ) (F : ℂ → ℝ) :
    (∫ z in Surface.disk, F z ∂ewAreaMeasure k) =
      ∫ z in Surface.disk, Surface.rho k z ^ 2 * F z := by
  rw [ewAreaMeasure,restrict_withDensity (s := Surface.disk) (show MeasurableSet Surface.disk from measurableSet_ball),
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_rho k).pow_const 2).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]

namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Gradient squared of an actual half-period field, using the inverse metric
of the immersion chart and the field's actual disk coordinate. -/
def halfPeriodGradSq (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) : ℝ :=
  chartInvMetricGradSq (R.centeredChart q.val) (R.halfPeriodCoordinate f)
    (R.diskHomeomorph q).val.val

/-- The norm of the actual second fundamental form at a half-period point. -/
def halfPeriodAbsA (R : PaperHalfPeriodRealization k)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) : ℝ :=
  let z := (R.diskHomeomorph q).val.val
  conformalSecondFundamentalNorm (R.centeredChart q.val) z
    (chartAreaDensity (R.centeredChart q.val) z)

lemma halfPeriodGradSq_eq (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    R.halfPeriodGradSq f q = (Surface.rho k (R.diskHomeomorph q).val.val ^ 2)⁻¹ *
      Surface.gradSq (R.halfPeriodCoordinate f) (R.diskHomeomorph q).val.val :=
  R.centeredChart_invMetricGradSq q.val (R.diskHomeomorph q).val
    (R.projection_agrees q).symm _

lemma halfPeriodAbsA_eq (R : PaperHalfPeriodRealization k)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    R.halfPeriodAbsA q = Surface.absA k (R.diskHomeomorph q).val.val := by
  dsimp only [halfPeriodAbsA]
  rw [R.centeredChart_areaDensity q.val (R.diskHomeomorph q).val (R.projection_agrees q).symm]
  exact (R.centeredChart_finite_curvature q.val (R.diskHomeomorph q).val
    (R.projection_agrees q).symm).2

lemma integral_halfPeriodGradSq (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) :
    (∫ q, R.halfPeriodGradSq f q ∂(R.halfPeriodArea)) =
      Surface.dirichletG k (R.halfPeriodCoordinate f) := by
  simp_rw [halfPeriodGradSq_eq]
  rw [R.integral_halfPeriodArea_coordinate (fun z =>
    (Surface.rho k z ^ 2)⁻¹ * Surface.gradSq (R.halfPeriodCoordinate f) z),
    integral_ewAreaMeasure_disk_real]
  unfold Surface.dirichletG
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  dsimp only
  ring

lemma integral_halfPeriodPotential (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) :
    (∫ q, (R.halfPeriodAbsA q * ‖f q‖)^2 ∂(R.halfPeriodArea)) =
      Surface.potentialG k (R.halfPeriodCoordinate f) := by
  have he : ∀ q, R.halfPeriodCoordinate f (R.diskHomeomorph q).val.val = f q := by
    intro q
    exact (R.halfPeriodCoordinate_apply f (R.diskHomeomorph q)).trans
      (congrArg f (R.diskHomeomorph.symm_apply_apply q))
  simp_rw [halfPeriodAbsA_eq,← he]
  rw [R.integral_halfPeriodArea_coordinate (fun z =>
    (Surface.absA k z * ‖R.halfPeriodCoordinate f z‖)^2),
    integral_ewAreaMeasure_disk_real]
  unfold Surface.potentialG
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  dsimp only
  ring

/-- Signed Jacobi form using the actual half-period measure and immersion. -/
def halfPeriodIntegralJacobiQ (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) : ℝ :=
  (∫ q, R.halfPeriodGradSq f q ∂(R.halfPeriodArea)) -
    ∫ q, (R.halfPeriodAbsA q * ‖f q‖)^2 ∂(R.halfPeriodArea)

theorem halfPeriodIntegralJacobiQ_eq (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) :
    R.halfPeriodIntegralJacobiQ f = SingleDiskBridge.Qd k (R.halfPeriodCoordinate f) := by
  rw [halfPeriodIntegralJacobiQ,integral_halfPeriodGradSq,integral_halfPeriodPotential]
  rfl

theorem halfPeriodIntegralJacobiQ_eq_chart (R : PaperHalfPeriodRealization k)
    (f : PaperHalfPeriod h.out (reflectionBasepoint k) R.C → ℂ) :
    R.halfPeriodIntegralJacobiQ f = R.halfPeriodChartJacobiQ (R.halfPeriodCoordinate f) :=
  (R.halfPeriodIntegralJacobiQ_eq f).trans (R.halfPeriodChartJacobiQ_eq _).symm

end PaperHalfPeriodRealization
end KsIndex.KarcherData
