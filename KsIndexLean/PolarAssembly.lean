module

/-
Per-circle Parseval identities for the value, radial derivative and angular derivative.

For `G : ℂ → ℂ` and a fixed real parameter `r`, the three normalized angular integrals
equal the corresponding mode sums:

* `hasSum_normSq_slice` — `∑_ℓ ‖Fm G ℓ r‖² = (2π)⁻¹ ∫₀^{2π} ‖G(r e^{iθ})‖² dθ`;
* `hasSum_normSq_dR` — `∑_ℓ ‖FmD G ℓ r‖² = (2π)⁻¹ ∫₀^{2π} ‖∂_r G(r e^{iθ})‖² dθ`;
* `hasSum_dTheta` — `∑_ℓ ℓ² ‖Fm G ℓ r‖² = (2π)⁻¹ ∫₀^{2π} ‖∂_θ G(r e^{iθ})‖² dθ`
  (from `fc_deriv`: the Fourier coefficient of `∂_θ` is `iℓ` times that of the slice).

The value identity assumes global continuity; the derivative identities assume global `C¹`
regularity. All three allow arbitrary real `r`. Combining them with `r_mul_gradSq_polar`
gives the per-circle Dirichlet sum for `r ≠ 0`. The separate potential sum assumes
continuity and `r ≥ 0`. Both use the normalization `(2π)⁻¹`. Radial integration and
interchange with the mode sum are not performed in this file.
-/
public import KsIndexLean.PolarGrad
public import KsIndexLean.RadialMode

@[expose] public section


noncomputable section

open Complex Real MeasureTheory intervalIntegral
open KsIndex.Parseval KsIndex.FourierMode KsIndex.PolarGrad KsIndex.Surface KsIndex.Radial

namespace KsIndex.PolarAssembly

variable {k : ℕ}

/-- `‖I · ℓ · z‖² = ℓ² ‖z‖²`. -/
lemma norm_I_mul_int_sq (ℓ : ℤ) (z : ℂ) : ‖I * (ℓ : ℂ) * z‖ ^ 2 = (ℓ : ℝ) ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, mul_pow]
  congr 1
  rw [show ((ℓ : ℤ) : ℂ) = (((ℓ : ℤ) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-! ### Continuity and periodicity of the slice and its derivative fields -/

/-- The radial-derivative field `θ ↦ ∂_r G(r e^{iθ}) = fderiv G (r e^{iθ}) (e^{iθ})`. -/
def dR (G : ℂ → ℂ) (r : ℝ) : ℝ → ℂ :=
  fun θ => fderiv ℝ G ((r : ℂ) * Complex.exp (θ * I)) (Complex.exp (θ * I))

/-- The angular-derivative field `θ ↦ ∂_θ G(r e^{iθ}) = fderiv G (r e^{iθ}) (r·(e^{iθ}·I))`. -/
def dTheta (G : ℂ → ℂ) (r : ℝ) : ℝ → ℂ :=
  fun θ => fderiv ℝ G ((r : ℂ) * Complex.exp (θ * I)) ((r : ℂ) * (Complex.exp (θ * I) * I))

lemma continuous_slice {G : ℂ → ℂ} (hG : Continuous G) (r : ℝ) : Continuous (slice G r) := by
  unfold slice; exact hG.comp (by fun_prop)

lemma continuous_dR {G : ℂ → ℂ} (hG : ContDiff ℝ 1 G) (r : ℝ) : Continuous (dR G r) := by
  unfold dR
  have hfd : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  exact (hfd.comp (by fun_prop)).clm_apply (by fun_prop)

lemma continuous_dTheta {G : ℂ → ℂ} (hG : ContDiff ℝ 1 G) (r : ℝ) : Continuous (dTheta G r) := by
  unfold dTheta
  have hfd : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  exact (hfd.comp (by fun_prop)).clm_apply (by fun_prop)

lemma slice_periodic {G : ℂ → ℂ} (r : ℝ) : Function.Periodic (slice G r) (2 * π) := by
  intro θ
  unfold slice
  rw [show ((θ + 2 * π : ℝ) : ℂ) * I = (θ : ℂ) * I + ((2 * π : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_add,
    show ((2 * π : ℝ) : ℂ) * I = ((1 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ### The three Parseval identities on one circle -/

/-- **Parseval for the slice**: `∑_ℓ ‖Fm G ℓ r‖² = (2π)⁻¹ ∫₀^{2π} ‖G(r e^{iθ})‖² dθ`. -/
theorem hasSum_normSq_slice {G : ℂ → ℂ} (hG : Continuous G) (r : ℝ) :
    HasSum (fun ℓ : ℤ => ‖Fm G ℓ r‖ ^ 2)
      ((2 * π : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖slice G r θ‖ ^ 2) :=
  hasSum_sq_fc (continuous_slice hG r)

/-- **Parseval for the radial derivative**:
`∑_ℓ ‖FmD G ℓ r‖² = (2π)⁻¹ ∫₀^{2π} ‖∂_r G(r e^{iθ})‖² dθ`. -/
theorem hasSum_normSq_dR {G : ℂ → ℂ} (hG : ContDiff ℝ 1 G) (r : ℝ) :
    HasSum (fun ℓ : ℤ => ‖FmD G ℓ r‖ ^ 2)
      ((2 * π : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖dR G r θ‖ ^ 2) :=
  hasSum_sq_fc (continuous_dR hG r)

/-- **Parseval for the angular derivative**:
`∑_ℓ ℓ² ‖Fm G ℓ r‖² = (2π)⁻¹ ∫₀^{2π} ‖∂_θ G(r e^{iθ})‖² dθ`. -/
theorem hasSum_dTheta {G : ℂ → ℂ} (hG : ContDiff ℝ 1 G) (r : ℝ) :
    HasSum (fun ℓ : ℤ => (ℓ : ℝ) ^ 2 * ‖Fm G ℓ r‖ ^ 2)
      ((2 * π : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖dTheta G r θ‖ ^ 2) := by
  have hd : ∀ θ, HasDerivAt (slice G r) (dTheta G r θ) θ := fun θ =>
    hasDerivAt_sliceθ hG r θ
  have hcoeff : ∀ ℓ : ℤ, fc (dTheta G r) ℓ = I * (ℓ : ℂ) * Fm G ℓ r := fun ℓ =>
    fc_deriv hd (continuous_dTheta hG r) (slice_periodic r) ℓ
  have h := hasSum_sq_fc (continuous_dTheta hG r)
  have hfun : (fun ℓ : ℤ => ‖fc (dTheta G r) ℓ‖ ^ 2)
      = fun ℓ : ℤ => (ℓ : ℝ) ^ 2 * ‖Fm G ℓ r‖ ^ 2 := by
    funext ℓ; rw [hcoeff ℓ, norm_I_mul_int_sq]
  rwa [hfun] at h

/-! ### The per-circle Dirichlet and potential mode sums

Combining the polar identity `r_mul_gradSq_polar` with the three Parseval identities: over one
circle the Dirichlet density integrates to `2π ∑_ℓ dirTerm ℓ r` and the potential density to
`2π ∑_ℓ potTerm ℓ r`. For positive radii these are the nonnegative families used in
the later radial integral/sum interchange; the Dirichlet identity itself allows any `r ≠ 0`. -/

/-- The per-mode Dirichlet density in the radius: `r‖∂_r Fm‖² + r⁻¹ℓ²‖Fm‖²`. -/
def dirTerm (G : ℂ → ℂ) (ℓ : ℤ) (r : ℝ) : ℝ :=
  r * ‖FmD G ℓ r‖ ^ 2 + r⁻¹ * ((ℓ : ℝ) ^ 2 * ‖Fm G ℓ r‖ ^ 2)

/-- The per-mode potential density in the radius: `r·V·‖Fm‖²`. -/
def potTerm (k : ℕ) (G : ℂ → ℂ) (ℓ : ℤ) (r : ℝ) : ℝ :=
  r * Vrad k r * ‖Fm G ℓ r‖ ^ 2

/-- **Per-circle Dirichlet mode sum**: `∑_ℓ dirTerm ℓ r = (2π)⁻¹ ∫₀^{2π} r·|∇G|²(r e^{iθ})`. -/
theorem hasSum_dirTerm {G : ℂ → ℂ} (hG : ContDiff ℝ 1 G) {r : ℝ} (hr : r ≠ 0) :
    HasSum (fun ℓ : ℤ => dirTerm G ℓ r)
      ((2 * π : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, r * gradSq G ((r : ℂ) * Complex.exp (θ * I))) := by
  have hcont1 : Continuous fun θ : ℝ => ‖dR G r θ‖ ^ 2 := (continuous_dR hG r).norm.pow 2
  have hcont2 : Continuous fun θ : ℝ => ‖dTheta G r θ‖ ^ 2 := (continuous_dTheta hG r).norm.pow 2
  have hpt : ∀ θ : ℝ, r * gradSq G ((r : ℂ) * Complex.exp (θ * I))
      = r * ‖dR G r θ‖ ^ 2 + r⁻¹ * ‖dTheta G r θ‖ ^ 2 := fun θ => by
    rw [r_mul_gradSq_polar G hr θ]; rfl
  have hf : IntervalIntegrable (fun θ : ℝ => r * ‖dR G r θ‖ ^ 2) volume 0 (2 * π) :=
    ((continuous_const.mul hcont1).intervalIntegrable _ _ :
      IntervalIntegrable (fun θ : ℝ => r * ‖dR G r θ‖ ^ 2) volume 0 (2 * π))
  have hg : IntervalIntegrable (fun θ : ℝ => r⁻¹ * ‖dTheta G r θ‖ ^ 2) volume 0 (2 * π) :=
    ((continuous_const.mul hcont2).intervalIntegrable _ _ :
      IntervalIntegrable (fun θ : ℝ => r⁻¹ * ‖dTheta G r θ‖ ^ 2) volume 0 (2 * π))
  have hInt : (∫ θ in (0 : ℝ)..2 * π, r * gradSq G ((r : ℂ) * Complex.exp (θ * I)))
      = r * (∫ θ in (0 : ℝ)..2 * π, ‖dR G r θ‖ ^ 2)
        + r⁻¹ * (∫ θ in (0 : ℝ)..2 * π, ‖dTheta G r θ‖ ^ 2) := by
    rw [intervalIntegral.integral_congr (fun θ _ => hpt θ),
      intervalIntegral.integral_add hf hg,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hsummand : (fun ℓ : ℤ => dirTerm G ℓ r)
      = fun ℓ : ℤ => r * ‖FmD G ℓ r‖ ^ 2 + r⁻¹ * ((ℓ : ℝ) ^ 2 * ‖Fm G ℓ r‖ ^ 2) := by
    funext ℓ; rw [dirTerm]
  rw [hsummand,
    show (2 * π : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, r * gradSq G ((r : ℂ) * Complex.exp (θ * I))
        = r * ((2 * π : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖dR G r θ‖ ^ 2)
          + r⁻¹ * ((2 * π : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖dTheta G r θ‖ ^ 2) from by
        rw [hInt]; ring]
  exact ((hasSum_normSq_dR hG r).mul_left r).add ((hasSum_dTheta hG r).mul_left r⁻¹)

/-- **Per-circle potential mode sum**: `∑_ℓ potTerm ℓ r = (2π)⁻¹ ∫₀^{2π} r·V·‖G(r e^{iθ})‖²`. -/
theorem hasSum_potTerm {G : ℂ → ℂ} (hG : Continuous G) {r : ℝ} (hr : 0 ≤ r) :
    HasSum (fun ℓ : ℤ => potTerm k G ℓ r)
      ((2 * π : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
        r * (potV k ((r : ℂ) * Complex.exp (θ * I))
          * ‖G ((r : ℂ) * Complex.exp (θ * I))‖ ^ 2)) := by
  have hInt : (∫ θ in (0 : ℝ)..2 * π,
        r * (potV k ((r : ℂ) * Complex.exp (θ * I))
          * ‖G ((r : ℂ) * Complex.exp (θ * I))‖ ^ 2))
      = (r * Vrad k r) * ∫ θ in (0 : ℝ)..2 * π, ‖slice G r θ‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    have hpv : potV k ((r : ℂ) * Complex.exp (θ * I)) = Vrad k r := by
      rw [potV_eq_Vrad, norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hr]
    rw [hpv, ← mul_assoc]; rfl
  have hsummand : (fun ℓ : ℤ => potTerm k G ℓ r)
      = fun ℓ : ℤ => (r * Vrad k r) * ‖Fm G ℓ r‖ ^ 2 := by
    funext ℓ; rw [potTerm, mul_assoc]
  rw [hsummand,
    show (2 * π : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
          r * (potV k ((r : ℂ) * Complex.exp (θ * I))
            * ‖G ((r : ℂ) * Complex.exp (θ * I))‖ ^ 2)
        = (r * Vrad k r) * ((2 * π : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖slice G r θ‖ ^ 2) from by
        rw [hInt]; ring]
  exact (hasSum_normSq_slice hG r).mul_left (r * Vrad k r)

end KsIndex.PolarAssembly
