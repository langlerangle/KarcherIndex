module

public import KsIndexLean.KarcherHomothetyCurvature

@[expose] public section


/-! Scaling of the conformal-chart Jacobi operator under ambient homothety. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace KsIndex.KarcherData

lemma conformalLaplaceBeltrami_coeff_germ {a b : ℂ → ℝ} {w : ℂ}
    (he : a =ᶠ[𝓝 w] b) (f : ℂ → ℂ) :
    conformalLaplaceBeltrami a f w = conformalLaplaceBeltrami b f w := by
  have hv (v : ℂ) :
      (fun z => (↑(a z) * (↑(a z))⁻¹ : ℂ) * fderiv ℝ f z v) =ᶠ[𝓝 w]
      (fun z => (↑(b z) * (↑(b z))⁻¹ : ℂ) * fderiv ℝ f z v) := by
    filter_upwards [he] with z hz
    rw [hz]
  unfold conformalLaplaceBeltrami
  rw [he.self_of_nhds, (hv 1).fderiv_eq, (hv Complex.I).fderiv_eq]

lemma conformalLaplaceBeltrami_scale (a : ℂ → ℝ) (f : ℂ → ℂ) (w : ℂ)
    {c : ℝ} (hc : c ≠ 0) :
    conformalLaplaceBeltrami (fun z => c ^ 2 * a z) f w =
      ((c ^ 2)⁻¹ : ℝ) * conformalLaplaceBeltrami a f w := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hf (z : ℂ) : (↑(c ^ 2 * a z) * (↑(c ^ 2 * a z))⁻¹ : ℂ) =
      ↑(a z) * (↑(a z))⁻¹ := by
    push_cast
    rw [mul_inv_rev]
    calc
      _ = ((c : ℂ)^2 * ((c : ℂ)^2)⁻¹) * ((a z : ℂ) * (a z : ℂ)⁻¹) := by ring
      _ = _ := by simp [hc']
  unfold conformalLaplaceBeltrami
  simp_rw [hf]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_inv, mul_inv_rev]
  ring

lemma conformalSecondFundamentalNorm_sq (X : ℂ → AmbientTriple) (w : ℂ) (s : ℝ) :
    conformalSecondFundamentalNorm X w s ^ 2 = conformalSecondFundamentalNormSq X w s := by
  apply Real.sq_sqrt
  unfold conformalSecondFundamentalNormSq
  positivity

/-- Jacobi-operator expression for conformal chart coordinates, using the induced
area density and second fundamental form. The definition is total for any `X`;
its geometric interpretation uses conformality of the chart. -/
def chartJacobiOperator (X : ℂ → AmbientTriple) (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  conformalLaplaceBeltrami (chartAreaDensity X) f w +
    (conformalSecondFundamentalNorm X w (chartAreaDensity X w) : ℂ)^2 * f w

lemma chartJacobiOperator_homothety {X : ℂ → AmbientTriple} {w : ℂ}
    (hX : ContDiffAt ℝ 2 X w)
    (hnear : ∀ᶠ z in 𝓝 w, DifferentiableAt ℝ X z)
    {c : ℝ} (hc : c ≠ 0) (f : ℂ → ℂ) :
    chartJacobiOperator (c • X) f w = ((c ^ 2)⁻¹ : ℝ) * chartJacobiOperator X f w := by
  have he : chartAreaDensity (c • X) =ᶠ[𝓝 w] (fun z => c ^ 2 * chartAreaDensity X z) := by
    filter_upwards [hnear] with z hz
    exact chartAreaDensity_homothety hz c
  unfold chartJacobiOperator
  rw [conformalLaplaceBeltrami_coeff_germ he, conformalLaplaceBeltrami_scale _ _ _ hc]
  simp only [← Complex.ofReal_pow, conformalSecondFundamentalNorm_sq]
  rw [chartAreaDensity_homothety (hX.differentiableAt (by norm_num)),
    conformalSecondFundamentalNormSq_homothety hX hc]
  push_cast
  ring

end KsIndex.KarcherData
#print axioms KsIndex.KarcherData.conformalLaplaceBeltrami_scale
#print axioms KsIndex.KarcherData.chartJacobiOperator_homothety
