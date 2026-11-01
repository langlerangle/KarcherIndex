module

public import KsIndexLean.KarcherHalfPeriodClassical
public import KsIndexLean.SingleDiskBridge

@[expose] public section


/-! Half-period chart integrals computed from the actual EW immersion's
inverse metric, second fundamental form, and area density. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]
attribute [local instance] Classical.propDecidable

/-- Weighted gradient density in the actual immersion chart. The scalar
function is expressed in the finite parameter coordinate. -/
def halfPeriodDirichletDensity (R : PaperHalfPeriodRealization k)
    (u : ℂ → ℂ) (w : PuncturedClosedDisk k) : ℝ :=
  let X := R.centeredChart (R.diskHomeomorph.symm w).val
  chartInvMetricGradSq X u w.val.val * chartAreaDensity X w.val.val

/-- Weighted potential density using the actual second fundamental form. -/
def halfPeriodPotentialDensity (R : PaperHalfPeriodRealization k)
    (u : ℂ → ℂ) (w : PuncturedClosedDisk k) : ℝ :=
  let X := R.centeredChart (R.diskHomeomorph.symm w).val
  (conformalSecondFundamentalNorm X w.val.val (chartAreaDensity X w.val.val) *
    ‖u w.val.val‖)^2 * chartAreaDensity X w.val.val

lemma halfPeriodDirichletDensity_eq (R : PaperHalfPeriodRealization k)
    (u : ℂ → ℂ) (w : PuncturedClosedDisk k) :
    R.halfPeriodDirichletDensity u w = Surface.gradSq u w.val.val :=
  R.centeredChart_dirichletDensity_finite _ w.val (R.diskHomeomorph_symm_projection w) u

lemma halfPeriodPotentialDensity_eq (R : PaperHalfPeriodRealization k)
    (u : ℂ → ℂ) (w : PuncturedClosedDisk k) :
    R.halfPeriodPotentialDensity u w =
      (Surface.absA k w.val.val * ‖u w.val.val‖)^2 * Surface.rho k w.val.val ^2 := by
  dsimp only [halfPeriodPotentialDensity]
  rw [R.centeredChart_areaDensity _ w.val (R.diskHomeomorph_symm_projection w),
    (R.centeredChart_finite_curvature _ w.val (R.diskHomeomorph_symm_projection w)).2]

/-- The Dirichlet integral on the single open half-period, in its finite
parameter chart and with the actual induced area density. -/
def halfPeriodChartDirichlet (R : PaperHalfPeriodRealization k) (u : ℂ → ℂ) : ℝ :=
  ∫ z in Surface.disk, if hz : ‖z‖ ≤ 1 ∧ z ∉ Surface.punctures k then
    R.halfPeriodDirichletDensity u ⟨⟨z,hz.2⟩,hz.1⟩ else 0

/-- The curvature potential integral in the same actual immersion chart. -/
def halfPeriodChartPotential (R : PaperHalfPeriodRealization k) (u : ℂ → ℂ) : ℝ :=
  ∫ z in Surface.disk, if hz : ‖z‖ ≤ 1 ∧ z ∉ Surface.punctures k then
    R.halfPeriodPotentialDensity u ⟨⟨z,hz.2⟩,hz.1⟩ else 0

/-- Signed difference of the actual chart's gradient and curvature integrals. -/
def halfPeriodChartJacobiQ (R : PaperHalfPeriodRealization k) (u : ℂ → ℂ) : ℝ :=
  R.halfPeriodChartDirichlet u - R.halfPeriodChartPotential u

lemma halfPeriodChartDirichlet_eq (R : PaperHalfPeriodRealization k) (u : ℂ → ℂ) :
    R.halfPeriodChartDirichlet u = Surface.dirichletG k u := by
  unfold halfPeriodChartDirichlet Surface.dirichletG
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  have hp := Surface.punctures_notMem_disk (k := k) (by have := h.out; omega) hz
  have hn := (SurfaceForm.mem_disk_iff.mp hz).le
  dsimp only
  rw [dite_eq_left ⟨hn,hp⟩]
  exact (R.halfPeriodDirichletDensity_eq u ⟨⟨z,hp⟩,hn⟩).trans
    (div_mul_cancel₀ _ (rho_sq_pos h.out hp).ne').symm

lemma halfPeriodChartPotential_eq (R : PaperHalfPeriodRealization k) (u : ℂ → ℂ) :
    R.halfPeriodChartPotential u = Surface.potentialG k u := by
  unfold halfPeriodChartPotential Surface.potentialG
  apply setIntegral_congr_fun measurableSet_ball
  intro z hz
  have hp := Surface.punctures_notMem_disk (k := k) (by have := h.out; omega) hz
  dsimp only
  rw [dite_eq_left ⟨(SurfaceForm.mem_disk_iff.mp hz).le,hp⟩]
  exact R.halfPeriodPotentialDensity_eq u ⟨⟨z,hp⟩,(SurfaceForm.mem_disk_iff.mp hz).le⟩

/-- Exact form equality, with no half-period averaging or factor of two. -/
theorem halfPeriodChartJacobiQ_eq (R : PaperHalfPeriodRealization k) (u : ℂ → ℂ) :
    R.halfPeriodChartJacobiQ u = SingleDiskBridge.Qd k u := by
  rw [halfPeriodChartJacobiQ,halfPeriodChartDirichlet_eq,halfPeriodChartPotential_eq]
  rfl

end KsIndex.KarcherData.PaperHalfPeriodRealization
