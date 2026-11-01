module

public import KsIndexLean.KarcherCurvature

@[expose] public section


/-! Gaussian curvature from the actual first and second fundamental forms. -/
noncomputable section
namespace KsIndex.KarcherData

/-- The determinant of the shape operator in real coordinate directions.
The denominator is the determinant of the induced first fundamental form. -/
def chartGaussianCurvature (X : ℂ → AmbientTriple) (w : ℂ) : ℝ :=
  (secondFundamentalForm X w 1 1 * secondFundamentalForm X w Complex.I Complex.I -
    secondFundamentalForm X w 1 Complex.I * secondFundamentalForm X w Complex.I 1) /
  (firstFundamentalForm X w 1 1 * firstFundamentalForm X w Complex.I Complex.I -
    firstFundamentalForm X w 1 Complex.I ^ 2)

/-- Harmonic conformal immersions have Gaussian curvature minus half the
squared metric norm of their Hessian-defined second fundamental form. -/
theorem chartGaussianCurvature_eq_neg_half_normSq
    {X : ℂ → AmbientTriple} {U : Set ℂ} (h : HarmonicCoordinates X U)
    {w : ℂ} (hw : w ∈ U) {q : ℝ} (hq : 0 < q)
    (hm : ∀ d : ℂ, euclideanSq (fderiv ℝ X w d) = q * ‖d‖ ^ 2) :
    chartGaussianCurvature X w = -(conformalSecondFundamentalNormSq X w q) / 2 := by
  obtain ⟨hE, hF, hG⟩ := metric_coefficients_of_conformal hm
  have ht := secondFundamentalForm_trace_zero h hw
  have hs := secondFundamentalForm_symmetric h hw Complex.I 1
  have hd : secondFundamentalForm X w Complex.I Complex.I =
      -secondFundamentalForm X w 1 1 := by linarith
  unfold chartGaussianCurvature firstFundamentalForm conformalSecondFundamentalNormSq
  rw [hE, hF, hG, hd, hs]
  have hn := hq.ne'
  field_simp
  ring

/-- The Gaussian curvature formula for a genuine harmonic EW representative. -/
theorem ew_chartGaussianCurvature_eq {k : ℕ} (hk : 2 ≤ k)
    {X : ℂ → AmbientTriple} {U : Set ℂ} (hU : IsOpen U)
    (havoid : ∀ z ∈ U, z ∉ Surface.punctures k)
    (hd : ∀ z ∈ U, HasFDerivAt X (ewRealDifferential k z) z)
    (hH : HarmonicCoordinates X U) {w : ℂ} (hw : w ∈ U)
    (hX : ContDiffAt ℝ 2 X w) :
    chartGaussianCurvature X w = -(Surface.absA k w ^ 2) / 2 := by
  have hm (d : ℂ) : euclideanSq (fderiv ℝ X w d) =
      Surface.rho k w ^ 2 * ‖d‖ ^ 2 := by
    rw [(hd w hw).fderiv, ewRealDifferential_metric hk]
  rw [chartGaussianCurvature_eq_neg_half_normSq hH hw
    (rho_sq_pos hk (havoid w hw)) hm,
    ew_secondFundamentalNormSq_eq_absA_sq hk hU havoid hd hw hX]

end KsIndex.KarcherData
