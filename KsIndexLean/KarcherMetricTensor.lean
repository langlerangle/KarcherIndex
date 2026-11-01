module

public import KsIndexLean.KarcherConformalCovering

@[expose] public section


/-! The explicit bilinear induced metric in covering coordinates. -/
noncomputable section
namespace KsIndex.KarcherData

lemma euclideanDot_of_conformal {D : ℂ →L[ℝ] AmbientTriple} {s : ℝ}
    (hm : ∀ v : ℂ, euclideanSq (D v) = s * ‖v‖ ^ 2) (a b : ℂ) :
    euclideanDot (D a) (D b) = s * (a.re * b.re + a.im * b.im) := by
  obtain ⟨h1, hf, hi⟩ := metric_coefficients_of_conformal hm
  rw [real_linear_complex_components D a, real_linear_complex_components D b]
  simp only [euclideanDot, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at *
  linear_combination a.re * b.re * h1 + (a.re * b.im + a.im * b.re) * hf +
    a.im * b.im * hi

open scoped KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The bilinear first fundamental form, with the finite or infinity chart
chosen by the actual atlas at each point. -/
theorem centeredChart_metric_tensor (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (a b : ℂ) :
    firstFundamentalForm (R.centeredChart q) (R.chartCenter q) a b =
      Surface.rho k (R.chartCenter q) ^ 2 * (a.re * b.re + a.im * b.im) :=
  euclideanDot_of_conformal (R.centeredChart_metric q).2 a b

end PaperHalfPeriodRealization
end KsIndex.KarcherData
