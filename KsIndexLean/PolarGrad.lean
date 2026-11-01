module

/-
Polar decomposition of the flat gradient density for functions `ℂ → ℂ`.

The flat gradient density `gradSq G w = ‖∂_x G‖² + ‖∂_y G‖²` is the Hilbert–Schmidt norm² of the
`ℝ`-linear map `fderiv ℝ G w`, hence independent of the orthonormal basis used to compute it.
Rotating the standard basis `{1, I}` by a unit `a` gives `{a, a·I}`:

  `gradSq_rotBasis` : `gradSq G w = ‖fderiv ℝ G w a‖² + ‖fderiv ℝ G w (a·I)‖²`   (`‖a‖ = 1`).

Taking `a = e^{iθ}` and `w = r e^{iθ}` this is the polar identity
`|∇G|² = |∂_r G|² + r⁻²|∂_θ G|²` (the `r⁻²` is supplied when `∂_θ` pulls out the factor `r`);
`GradOrtho.basis_rot` supplies the linear algebra. The identities expressed using `fderiv`
require no differentiability hypothesis; the angular slice derivative theorem assumes global
`C¹` regularity. The weighted pointwise identity holds for every nonzero real `r`.
-/
public import KsIndexLean.GradOrtho
public import KsIndexLean.FourierMode

@[expose] public section


noncomputable section

open Complex Real

namespace KsIndex.PolarGrad

open KsIndex.Surface KsIndex.GradOrtho KsIndex.FourierMode

/-- **Basis-rotation form of the gradient density.**  For any unit `a`, the flat gradient density
of `G` at `w` is the sum of the squared directional derivatives along the rotated orthonormal basis
`{a, a·I}`.  (No differentiability hypothesis: `fderiv` is a continuous linear map either way.) -/
lemma gradSq_rotBasis (G : ℂ → ℂ) {a : ℂ} (ha : ‖a‖ = 1) (w : ℂ) :
    gradSq G w = ‖fderiv ℝ G w a‖ ^ 2 + ‖fderiv ℝ G w (a * I)‖ ^ 2 := by
  have hcz : ∀ z : ℂ, starRingEnd ℂ z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hb := basis_rot (fderiv ℝ G w) (fderiv ℝ G w) ha
  simp only [mul_one] at hb
  rw [hcz, hcz, hcz, hcz, ← Complex.ofReal_add, ← Complex.ofReal_add] at hb
  have h2 := Complex.ofReal_inj.mp hb
  rw [gradSq]; exact h2

/-- The `θ`-derivative of the slice `θ ↦ G(r e^{iθ})` is `fderiv ℝ G (r e^{iθ}) (r·(e^{iθ}·I))`
(the directional derivative along the tangent `r i e^{iθ}` to the circle of radius `r`). -/
lemma hasDerivAt_sliceθ {G : ℂ → ℂ} (hG : ContDiff ℝ 1 G) (r θ : ℝ) :
    HasDerivAt (slice G r)
      (fderiv ℝ G ((r : ℂ) * Complex.exp (θ * I)) ((r : ℂ) * (Complex.exp (θ * I) * I))) θ := by
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * I))
      (Complex.exp ((θ : ℂ) * I) * I) θ := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I θ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const I
    simpa using h1.cexp
  have hinner : HasDerivAt (fun t : ℝ => (r : ℂ) * Complex.exp ((t : ℂ) * I))
      ((r : ℂ) * (Complex.exp ((θ : ℂ) * I) * I)) θ := hexp.const_mul (r : ℂ)
  exact ((hG.differentiable one_ne_zero _).hasFDerivAt).comp_hasDerivAt θ hinner

/-- **Pointwise polar identity for the Dirichlet density.**  For `r ≠ 0`,
`r·|∇G|²(r e^{iθ}) = r·|∂_r G|² + r⁻¹·|∂_θ G|²`, with the radial and angular directional
derivatives written as `fderiv`-applications (`∂_θ` carries the tangent factor `r`). -/
lemma r_mul_gradSq_polar (G : ℂ → ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    r * gradSq G ((r : ℂ) * Complex.exp (θ * I))
      = r * ‖fderiv ℝ G ((r : ℂ) * Complex.exp (θ * I)) (Complex.exp (θ * I))‖ ^ 2
        + r⁻¹ * ‖fderiv ℝ G ((r : ℂ) * Complex.exp (θ * I))
            ((r : ℂ) * (Complex.exp (θ * I) * I))‖ ^ 2 := by
  rw [gradSq_rotBasis G (norm_exp_I_mul θ) ((r : ℂ) * Complex.exp (θ * I))]
  have h2 : ‖fderiv ℝ G ((r : ℂ) * Complex.exp (θ * I)) ((r : ℂ) * (Complex.exp (θ * I) * I))‖ ^ 2
      = r ^ 2 * ‖fderiv ℝ G ((r : ℂ) * Complex.exp (θ * I)) (Complex.exp (θ * I) * I)‖ ^ 2 := by
    rw [show (r : ℂ) * (Complex.exp (θ * I) * I) = (r : ℝ) • (Complex.exp (θ * I) * I) from
        Complex.real_smul.symm, map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [h2]
  field_simp

end KsIndex.PolarGrad
