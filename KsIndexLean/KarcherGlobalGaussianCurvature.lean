module

public import KsIndexLean.KarcherGaussianCurvature
public import KsIndexLean.KarcherActualChartOverlap

@[expose] public section


/-! Gaussian curvature of the actual normalized EW immersion in its atlas. -/
noncomputable section
open scoped ContDiff KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData

lemma secondFundamentalForm_symmetric_of_contDiffAt
    {X : ℂ → AmbientTriple} {w : ℂ} (hX : ContDiffAt ℝ 2 X w) (u v : ℂ) :
    secondFundamentalForm X w u v = secondFundamentalForm X w v u := by
  have h1 := hX.fst.isSymmSndFDerivAt (by simp)
  have h2 := hX.snd.fst.isSymmSndFDerivAt (by simp)
  have h3 := hX.snd.snd.isSymmSndFDerivAt (by simp)
  have hb (f : ℂ → ℝ) (hf : IsSymmSndFDerivAt ℝ f w) :
      bilinearIteratedFDerivTwo ℝ f w u v = bilinearIteratedFDerivTwo ℝ f w v u := hf u v
  simp only [secondFundamentalForm, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hb _ h1, hb _ h2, hb _ h3]

/-- A C² conformal minimal immersion has the same determinant identity,
without requiring harmonicity as an additional hypothesis. -/
lemma chartGaussianCurvature_eq_of_minimal {X : ℂ → AmbientTriple} {w : ℂ}
    (hX : ContDiffAt ℝ 2 X w) {q : ℝ} (hq : 0 < q)
    (hm : ∀ d : ℂ, euclideanSq (fderiv ℝ X w d) = q * ‖d‖ ^ 2)
    (hH : chartMeanCurvature X w = 0) :
    chartGaussianCurvature X w = -(conformalSecondFundamentalNormSq X w q) / 2 := by
  rw [chartMeanCurvature_conformal hq hm] at hH
  have ht : secondFundamentalForm X w 1 1 + secondFundamentalForm X w Complex.I Complex.I = 0 :=
    (div_eq_zero_iff.mp hH).resolve_right (by positivity)
  have hs := secondFundamentalForm_symmetric_of_contDiffAt hX Complex.I 1
  have hd : secondFundamentalForm X w Complex.I Complex.I =
      -secondFundamentalForm X w 1 1 := by linarith
  obtain ⟨hE, hF, hG⟩ := metric_coefficients_of_conformal hm
  unfold chartGaussianCurvature firstFundamentalForm conformalSecondFundamentalNormSq
  rw [hE, hF, hG, hd, hs]
  have hn := hq.ne'
  field_simp
  ring

namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The determinant-defined curvature formula holds at every atlas center,
including the chart over infinity. -/
theorem centeredChart_gaussianCurvature (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    chartGaussianCurvature (R.centeredChart q) (R.chartCenter q) =
      -(Surface.absA k (R.chartCenter q) ^ 2) / 2 := by
  have ht : R.chartCenter q ∈ (HeightLift.liftChart R.hC q).target :=
    (HeightLift.liftChart R.hC q).map_source (HeightLift.liftChart_mem R.hC q)
  have hc := R.centeredChart_curvature q
  obtain ⟨hq, hm⟩ := R.centeredChart_metric q
  rw [chartGaussianCurvature_eq_of_minimal
    ((R.centeredChart_contDiffAt q ht).of_le (by simp)) hq hm hc.1]
  have hn : 0 ≤ conformalSecondFundamentalNormSq (R.centeredChart q)
      (R.chartCenter q) (Surface.rho k (R.chartCenter q) ^ 2) := by
    unfold conformalSecondFundamentalNormSq
    positivity
  have he := Real.sq_sqrt hn
  change conformalSecondFundamentalNorm _ _ _ ^ 2 = _ at he
  rw [hc.2] at he
  rw [← he]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
