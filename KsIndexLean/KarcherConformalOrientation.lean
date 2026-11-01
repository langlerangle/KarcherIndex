module

public import KsIndexLean.KarcherNormalComparison

@[expose] public section


/-! Holomorphic nonzero coordinate derivatives preserve the actual normal. -/
noncomputable section
namespace KsIndex.KarcherData

lemma real_linear_complex_components (D : ℂ →L[ℝ] AmbientTriple) (z : ℂ) :
    D z = z.re • D 1 + z.im • D Complex.I := by
  have he : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  exact (congrArg D he).trans (by simp only [map_add, map_smul])

lemma euclideanCross_complex_change (D : ℂ →L[ℝ] AmbientTriple) (c : ℂ) :
    euclideanCross (D c) (D (c * Complex.I)) =
      Complex.normSq c • euclideanCross (D 1) (D Complex.I) := by
  have h1 := real_linear_complex_components D c
  have hi := real_linear_complex_components D (c * Complex.I)
  simp only [Complex.mul_I_re, Complex.mul_I_im] at hi
  rw [h1, hi]
  apply Prod.ext
  · simp only [euclideanCross, Complex.normSq_apply, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  · apply Prod.ext <;>
      simp only [euclideanCross, Complex.normSq_apply, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

lemma normalized_positive_smul (a : AmbientTriple) {r : ℝ} (hr : 0 < r) :
    (Real.sqrt (euclideanSq (r • a)))⁻¹ • (r • a) =
      (Real.sqrt (euclideanSq a))⁻¹ • a := by
  rw [euclideanSq_smul, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs,
    abs_of_pos hr, mul_inv_rev, smul_smul]
  congr 1
  rw [mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]

/-- The cross-product normal of a differential is unchanged by multiplication
of its complex input by a nonzero complex number. -/
theorem normal_of_complex_change (D : ℂ →L[ℝ] AmbientTriple) {c : ℂ} (hc : c ≠ 0) :
    (Real.sqrt (euclideanSq (euclideanCross (D c) (D (c * Complex.I)))))⁻¹ •
        euclideanCross (D c) (D (c * Complex.I)) =
      (Real.sqrt (euclideanSq (euclideanCross (D 1) (D Complex.I))))⁻¹ •
        euclideanCross (D 1) (D Complex.I) := by
  rw [euclideanCross_complex_change]
  exact normalized_positive_smul _ (Complex.normSq_pos.mpr hc)

/-- A smooth change of coordinates whose real derivative is nonzero complex
multiplication preserves the oriented normal of a parametrization. -/
theorem chartUnitNormal_comp_complex {X : ℂ → AmbientTriple} {f : ℂ → ℂ}
    {z c : ℂ} (hX : DifferentiableAt ℝ X (f z))
    (hf : DifferentiableAt ℝ f z) (hc : c ≠ 0)
    (hd : ∀ v : ℂ, fderiv ℝ f z v = c * v) :
    chartUnitNormal (X ∘ f) z = chartUnitNormal X (f z) := by
  simp only [chartUnitNormal, fderiv_comp z hX hf,
    ContinuousLinearMap.comp_apply, hd, mul_one]
  exact normal_of_complex_change _ hc

end KsIndex.KarcherData
