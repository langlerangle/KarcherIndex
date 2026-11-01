module

public import KsIndexLean.KarcherChartArea

@[expose] public section


/-! Ambient homotheties of the actual induced metric and area density. -/
noncomputable section
namespace KsIndex.KarcherData

lemma euclideanDot_smul_both (c : ℝ) (a b : AmbientTriple) :
    euclideanDot (c • a) (c • b) = c ^ 2 * euclideanDot a b := by
  simp only [euclideanDot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

lemma euclideanCross_smul_both (c : ℝ) (a b : AmbientTriple) :
    euclideanCross (c • a) (c • b) = c ^ 2 • euclideanCross a b := by
  ext <;> simp [euclideanCross, smul_eq_mul] <;> ring

lemma firstFundamentalForm_homothety {X : ℂ → AmbientTriple} {w : ℂ}
    (hX : DifferentiableAt ℝ X w) (c : ℝ) (u v : ℂ) :
    firstFundamentalForm (c • X) w u v = c ^ 2 * firstFundamentalForm X w u v := by
  simp only [firstFundamentalForm, fderiv_const_smul hX, smul_apply]
  exact euclideanDot_smul_both c _ _

lemma chartGramDet_homothety {X : ℂ → AmbientTriple} {w : ℂ}
    (hX : DifferentiableAt ℝ X w) (c : ℝ) :
    chartGramDet (c • X) w = c ^ 4 * chartGramDet X w := by
  simp only [chartGramDet, firstFundamentalForm_homothety hX]
  ring

lemma chartAreaDensity_homothety {X : ℂ → AmbientTriple} {w : ℂ}
    (hX : DifferentiableAt ℝ X w) (c : ℝ) :
    chartAreaDensity (c • X) w = c ^ 2 * chartAreaDensity X w := by
  rw [chartAreaDensity, chartGramDet_homothety hX]
  rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (sq_nonneg c)]
  rfl

lemma chartInvMetricGradSq_homothety {X : ℂ → AmbientTriple} {w : ℂ}
    (hX : DifferentiableAt ℝ X w) {c : ℝ} (hc : c ≠ 0) (f : ℂ → ℂ) :
    chartInvMetricGradSq (c • X) f w = (c ^ 2)⁻¹ * chartInvMetricGradSq X f w := by
  simp only [chartInvMetricGradSq, firstFundamentalForm_homothety hX,
    chartGramDet_homothety hX]
  by_cases hD : chartGramDet X w = 0
  · simp [hD]
  · field_simp

/-- The two-dimensional Dirichlet density is invariant under nonzero homothety. -/
lemma chartDirichletDensity_homothety {X : ℂ → AmbientTriple} {w : ℂ}
    (hX : DifferentiableAt ℝ X w) {c : ℝ} (hc : c ≠ 0) (f : ℂ → ℂ) :
    chartInvMetricGradSq (c • X) f w * chartAreaDensity (c • X) w =
      chartInvMetricGradSq X f w * chartAreaDensity X w := by
  rw [chartInvMetricGradSq_homothety hX hc, chartAreaDensity_homothety hX]
  field_simp

lemma chartUnitNormal_homothety {X : ℂ → AmbientTriple} {w : ℂ}
    (hX : DifferentiableAt ℝ X w) {c : ℝ} (hc : c ≠ 0) :
    chartUnitNormal (c • X) w = chartUnitNormal X w := by
  simp only [chartUnitNormal, fderiv_const_smul hX, smul_apply,
    euclideanCross_smul_both, euclideanSq_smul]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg c), mul_inv_rev, smul_smul]
  congr 1
  field_simp

end KsIndex.KarcherData
#print axioms KsIndex.KarcherData.chartAreaDensity_homothety
#print axioms KsIndex.KarcherData.chartInvMetricGradSq_homothety
#print axioms KsIndex.KarcherData.chartDirichletDensity_homothety
#print axioms KsIndex.KarcherData.chartUnitNormal_homothety
