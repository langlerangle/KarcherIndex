module

public import KsIndexLean.KarcherHomothetyMetric
public import KsIndexLean.KarcherCurvature

@[expose] public section


/-! Scaling of the Hessian-defined second fundamental form and curvature. -/
noncomputable section
open InnerProductSpace
open scoped ContDiff
namespace KsIndex.KarcherData

lemma coordinateHessian_homothety {f : ℂ → ℝ} {w : ℂ}
    (hf : ContDiffAt ℝ 2 f w) (c : ℝ) (u v : ℂ) :
    bilinearIteratedFDerivTwo ℝ (c • f) w u v =
      c * bilinearIteratedFDerivTwo ℝ f w u v := by
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    bilinearIteratedFDerivTwo_eq_iteratedFDeriv, iteratedFDeriv_const_smul_apply hf]
  rfl

lemma secondFundamentalForm_homothety {X : ℂ → AmbientTriple} {w : ℂ}
    (hX : ContDiffAt ℝ 2 X w) {c : ℝ} (hc : c ≠ 0) (u v : ℂ) :
    secondFundamentalForm (c • X) w u v = c * secondFundamentalForm X w u v := by
  simp only [secondFundamentalForm, chartUnitNormal_homothety
    (hX.differentiableAt (by norm_num)) hc, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul]
  have h1 := coordinateHessian_homothety hX.fst c u v
  have h2 := coordinateHessian_homothety hX.snd.fst c u v
  have h3 := coordinateHessian_homothety hX.snd.snd c u v
  change _ * bilinearIteratedFDerivTwo ℝ (c • fun z => (X z).1) w u v +
    _ * bilinearIteratedFDerivTwo ℝ (c • fun z => (X z).2.1) w u v +
    _ * bilinearIteratedFDerivTwo ℝ (c • fun z => (X z).2.2) w u v = _
  rw [h1,h2,h3]
  ring

lemma conformalSecondFundamentalNormSq_homothety {X : ℂ → AmbientTriple} {w : ℂ}
    (hX : ContDiffAt ℝ 2 X w) {c : ℝ} (hc : c ≠ 0) (s : ℝ) :
    conformalSecondFundamentalNormSq (c • X) w (c ^ 2 * s) =
      (c ^ 2)⁻¹ * conformalSecondFundamentalNormSq X w s := by
  simp only [conformalSecondFundamentalNormSq, secondFundamentalForm_homothety hX hc]
  by_cases hs : s = 0
  · simp [hs]
  · field_simp

/-- The curvature-potential density, like the Dirichlet density, is scale invariant. -/
lemma curvatureAreaDensity_homothety {X : ℂ → AmbientTriple} {w : ℂ}
    (hX : ContDiffAt ℝ 2 X w) {c : ℝ} (hc : c ≠ 0) :
    conformalSecondFundamentalNormSq (c • X) w (chartAreaDensity (c • X) w) *
      chartAreaDensity (c • X) w =
    conformalSecondFundamentalNormSq X w (chartAreaDensity X w) * chartAreaDensity X w := by
  rw [chartAreaDensity_homothety (hX.differentiableAt (by norm_num)),
    conformalSecondFundamentalNormSq_homothety hX hc]
  field_simp

end KsIndex.KarcherData
#print axioms KsIndex.KarcherData.secondFundamentalForm_homothety
#print axioms KsIndex.KarcherData.conformalSecondFundamentalNormSq_homothety
#print axioms KsIndex.KarcherData.curvatureAreaDensity_homothety
