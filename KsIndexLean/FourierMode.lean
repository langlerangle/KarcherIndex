module

/-
# Circular Fourier modes and rotation-class selection

For `F : ℂ → ℂ` and real radius parameter `r₀`, define
`slice F r₀ θ = F(r₀ e^{iθ})` and
`Fm F ℓ r₀ = (2π)⁻¹ ∫₀^{2π} F(r₀ e^{iθ}) e^{-iℓθ} dθ`.
Continuity of `F` gives continuity of each mode in `r₀`; a global `C¹`
hypothesis gives the radial derivative `FmD F ℓ` and its continuity.
At the center, every nonzero-frequency mode vanishes for any `F`.

For `k > 0`, membership in the rotation eigenspace `Erot1 k r` forces modes
outside `ℓ ≡ -r mod k` to vanish. This selection theorem follows directly from
the cyclic shift identity and the integral definition; its statement imposes
no continuity hypothesis. In particular, the invariant class `r = 0` allows
all frequencies divisible by `k`, not only the zero frequency.
-/
public import KsIndexLean.Parseval1
public import KsIndexLean.SingleDisk
public import KsIndexLean.SurfaceSym

@[expose] public section


noncomputable section

open Complex Real MeasureTheory intervalIntegral Set Filter Topology
open KsIndex.Parseval KsIndex.SingleDiskBridge KsIndex.SingleDisk KsIndex.FormIndex
  KsIndex.SurfaceSym
open scoped ContDiff

namespace KsIndex.FourierMode

variable {k : ℕ}

/-- The `θ`-slice of `F` at radius `r`: `θ ↦ F(r e^{iθ})`. -/
def slice (F : ℂ → ℂ) (r : ℝ) : ℝ → ℂ := fun θ => F ((r : ℂ) * Complex.exp (θ * I))

/-- The `ℓ`-th circular Fourier mode of `F` at radius `r`. -/
def Fm (F : ℂ → ℂ) (ℓ : ℤ) (r : ℝ) : ℂ := fc (slice F r) ℓ

/-- The `ℓ`-th Fourier mode of the radial-derivative field. For `C¹` functions,
`Fm_hasDerivAt` identifies this with the derivative of `Fm F ℓ` in the radius. -/
def FmD (F : ℂ → ℂ) (ℓ : ℤ) (r : ℝ) : ℂ :=
  fc (fun θ => fderiv ℝ F ((r : ℂ) * Complex.exp (θ * I)) (Complex.exp (θ * I))) ℓ

/-! ### Continuity in the radius -/

lemma continuous_slicePoint :
    Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * I) := by
  fun_prop

/-- `Fm F ℓ` is continuous in the radius (a parametric interval integral, `F` continuous). -/
lemma Fm_continuous {F : ℂ → ℂ} (hF : Continuous F) (ℓ : ℤ) : Continuous (Fm F ℓ) := by
  unfold Fm fc slice
  refine continuous_const.mul ?_
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ 0 (2 * π)
  refine Continuous.mul ?_ (by fun_prop)
  exact hF.comp (by fun_prop)

/-! ### Norms of the exponential factors -/

lemma norm_exp_I_mul (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * I)‖ = 1 := by
  rw [Complex.norm_exp]; simp

lemma norm_exp_neg_mul (ℓ : ℤ) (θ : ℝ) : ‖Complex.exp (-(ℓ : ℂ) * I * (θ : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-! ### Differentiation in the radius -/

/-- The derivative of `x ↦ F(x·v)` at `x`, `v` fixed, is `fderiv F (x·v) v`. -/
lemma hasDerivAt_comp_lineMul {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (v : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => F ((y : ℂ) * v)) (fderiv ℝ F ((x : ℂ) * v) v) x := by
  have hφ : HasDerivAt (fun y : ℝ => (y : ℂ) * v) v x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).mul_const v
  exact ((hF.differentiable one_ne_zero _).hasFDerivAt).comp_hasDerivAt x hφ

/-- The radial-derivative-field integrand is jointly continuous. -/
lemma continuous_FmD_integrand {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (ℓ : ℤ) :
    Continuous fun p : ℝ × ℝ =>
      fderiv ℝ F ((p.1 : ℂ) * Complex.exp (p.2 * I)) (Complex.exp (p.2 * I))
        * Complex.exp (-(ℓ : ℂ) * I * p.2) := by
  have hfd : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  have hpt : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * I) := by fun_prop
  have hexp : Continuous fun p : ℝ × ℝ => Complex.exp (p.2 * I) := by fun_prop
  exact ((hfd.comp hpt).clm_apply hexp).mul (by fun_prop)

/-- `FmD F ℓ` is continuous in the radius. -/
lemma FmD_continuous {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (ℓ : ℤ) : Continuous (FmD F ℓ) := by
  unfold FmD fc
  refine continuous_const.mul ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_FmD_integrand hF ℓ) 0 (2 * π)

/-- **`Fm F ℓ` is `C¹` in the radius**, with derivative `FmD F ℓ` (differentiation under the
integral sign; `F` of class `C¹`). -/
theorem Fm_hasDerivAt {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (ℓ : ℤ) (r : ℝ) :
    HasDerivAt (Fm F ℓ) (FmD F ℓ r) r := by
  set Ffun : ℝ → ℝ → ℂ :=
    fun x θ => F ((x : ℂ) * Complex.exp (θ * I)) * Complex.exp (-(ℓ : ℂ) * I * θ) with hFfun
  set F'fun : ℝ → ℝ → ℂ :=
    fun x θ => fderiv ℝ F ((x : ℂ) * Complex.exp (θ * I)) (Complex.exp (θ * I))
      * Complex.exp (-(ℓ : ℂ) * I * θ) with hF'fun
  have hFc : Continuous F := hF.continuous
  -- integrand continuity in `θ` for fixed `x`
  have hFfunθ : ∀ x : ℝ, Continuous (Ffun x) := by
    intro x; rw [hFfun]
    exact (hFc.comp (by fun_prop)).mul (by fun_prop)
  have hF'funθ : ∀ x : ℝ, Continuous (F'fun x) := by
    intro x; rw [hF'fun]
    have hfd : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
    exact ((hfd.comp (by fun_prop)).clm_apply (by fun_prop)).mul (by fun_prop)
  -- the uniform bound on the derivative field
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (|r| + 1)).exists_bound_of_continuousOn
    (hF.continuous_fderiv one_ne_zero).continuousOn
  have hbound : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Set.uIoc (0 : ℝ) (2 * π) →
      ∀ x ∈ Metric.ball r 1, ‖F'fun x θ‖ ≤ B := by
    refine Filter.Eventually.of_forall (fun θ _ x hx => ?_)
    rw [hF'fun]
    have hxb : (x : ℂ) * Complex.exp ((θ : ℂ) * I) ∈ Metric.closedBall (0 : ℂ) (|r| + 1) := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_exp_I_mul, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
      have hlt : |x - r| < 1 := by
        have h := Metric.mem_ball.1 hx; rwa [Real.dist_eq] at h
      have hxle : |x| - |r| ≤ |x - r| := abs_sub_abs_le_abs_sub x r
      linarith
    calc ‖fderiv ℝ F ((x : ℂ) * Complex.exp ((θ : ℂ) * I)) (Complex.exp ((θ : ℂ) * I))
            * Complex.exp (-(ℓ : ℂ) * I * (θ : ℂ))‖
        = ‖fderiv ℝ F ((x : ℂ) * Complex.exp ((θ : ℂ) * I)) (Complex.exp ((θ : ℂ) * I))‖ := by
          rw [norm_mul, norm_exp_neg_mul, mul_one]
      _ ≤ ‖fderiv ℝ F ((x : ℂ) * Complex.exp ((θ : ℂ) * I))‖ * ‖Complex.exp ((θ : ℂ) * I)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ F ((x : ℂ) * Complex.exp ((θ : ℂ) * I))‖ := by rw [norm_exp_I_mul, mul_one]
      _ ≤ B := hB _ hxb
  have hdiff : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Set.uIoc (0 : ℝ) (2 * π) →
      ∀ x ∈ Metric.ball r 1, HasDerivAt (fun x => Ffun x θ) (F'fun x θ) x := by
    refine Filter.Eventually.of_forall (fun θ _ x _ => ?_)
    rw [hFfun, hF'fun]
    exact (hasDerivAt_comp_lineMul hF (Complex.exp ((θ : ℂ) * I)) x).mul_const _
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ => B) (F := Ffun) (F' := F'fun) (x₀ := r) (a := 0) (b := 2 * π)
    (μ := volume) (s := Metric.ball r 1)
    (Metric.ball_mem_nhds r one_pos)
    (Filter.Eventually.of_forall fun x => (hFfunθ x).aestronglyMeasurable)
    ((hFfunθ r).intervalIntegrable _ _)
    ((hF'funθ r).aestronglyMeasurable)
    hbound (intervalIntegrable_const) hdiff
  have hgoal := hmain.2.const_mul (Complex.ofReal ((2 * π : ℝ)⁻¹))
  exact hgoal

/-! ### The value at the centre -/

/-- The integral of `e^{−iℓθ}` over a full period vanishes for `ℓ ≠ 0`. -/
lemma integral_exp_period (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    ∫ θ in (0 : ℝ)..2 * π, Complex.exp (-(ℓ : ℂ) * I * θ) = 0 := by
  have hc : (-(ℓ : ℂ) * I) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, neg_eq_zero, Complex.I_ne_zero, or_false]
    exact_mod_cast hℓ
  rw [integral_exp_mul_complex hc]
  have h2π : (-(ℓ : ℂ) * I) * ((2 * π : ℝ) : ℂ) = ((-ℓ : ℤ) : ℂ) * (2 * π * I) := by
    push_cast; ring
  rw [h2π, Complex.exp_int_mul_two_pi_mul_I]
  simp

/-- `Fm F ℓ 0 = 0` for `ℓ ≠ 0`: the slice at the centre is the constant `F 0`. -/
lemma Fm_zero_of_ne (F : ℂ → ℂ) {ℓ : ℤ} (hℓ : ℓ ≠ 0) : Fm F ℓ 0 = 0 := by
  unfold Fm fc slice
  have hs : (fun θ : ℝ => F ((0 : ℝ) * Complex.exp (θ * I)) * Complex.exp (-(ℓ : ℂ) * I * θ))
      = fun θ : ℝ => F 0 * Complex.exp (-(ℓ : ℂ) * I * θ) := by
    funext θ; simp
  rw [hs, intervalIntegral.integral_const_mul, integral_exp_period ℓ hℓ, mul_zero, mul_zero]

/-! ### Class selection under the rotation `Erot1` -/

/-- The rotation identity carried by an `Erot1 k r`-eigenfunction: `F(ζ_k⁻¹ w) = ζ_k^r F(w)`. -/
lemma rotEq_of_mem {F : ℂ → ℂ} {r : ℕ} (hF : F ∈ Erot1 k r) (w : ℂ) :
    F ((rotUnit k : ℂ) * w) = (zeta k) ^ r * F w := by
  rw [Erot1, Module.End.mem_eigenspace_iff] at hF
  have := congrFun hF w
  simpa [rot1] using this

/-- For rotation class `r`, the angular shift satisfies
`slice F r₀ (θ + 2π/k) = (ζ_k^r)⁻¹ · slice F r₀ θ`. -/
lemma slice_shift {F : ℂ → ℂ} {r : ℕ} (hF : F ∈ Erot1 k r) (r₀ θ : ℝ) :
    slice F r₀ (θ + 2 * π / k) = (zeta k ^ r)⁻¹ * slice F r₀ θ := by
  have hz : (zeta k) ^ r ≠ 0 := pow_ne_zero _ (by
    rw [zeta]; exact Complex.exp_ne_zero _)
  have hpt : (rotUnit k : ℂ) * ((r₀ : ℂ) * Complex.exp (((θ + 2 * π / k : ℝ) : ℂ) * I))
      = (r₀ : ℂ) * Complex.exp ((θ : ℂ) * I) := by
    rw [rotUnit, Circle.coe_exp]
    rw [show ((θ + 2 * π / k : ℝ) : ℂ) * I
      = (θ : ℂ) * I + ((2 * π / k : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_add]
    rw [show ((-(2 * π) / k : ℝ) : ℂ) * I = -(((2 * π / k : ℝ) : ℂ) * I) by push_cast; ring]
    rw [Complex.exp_neg,
      show (Complex.exp (((2 * π / k : ℝ) : ℂ) * I))⁻¹
          * ((r₀ : ℂ) * (Complex.exp ((θ : ℂ) * I) * Complex.exp (((2 * π / k : ℝ) : ℂ) * I)))
        = (r₀ : ℂ) * Complex.exp ((θ : ℂ) * I)
            * ((Complex.exp (((2 * π / k : ℝ) : ℂ) * I))⁻¹
                * Complex.exp (((2 * π / k : ℝ) : ℂ) * I)) by ring,
      inv_mul_cancel₀ (Complex.exp_ne_zero _), mul_one]
  have hrot := rotEq_of_mem hF ((r₀ : ℂ) * Complex.exp (((θ + 2 * π / k : ℝ) : ℂ) * I))
  rw [hpt] at hrot
  -- hrot : F(r₀ e^{iθ}) = ζ^r * F(r₀ e^{i(θ+2π/k)})
  unfold slice
  rw [hrot, ← mul_assoc, inv_mul_cancel₀ hz, one_mul]

/-- **Class selection.**  If `F ∈ Erot1 k r`, then every off-class Fourier mode of `F` vanishes:
`Fm F ℓ r₀ = 0` unless `k ∣ r + ℓ` (equivalently `ℓ ≡ −r mod k`). -/
theorem Fm_eq_zero_of_class {F : ℂ → ℂ} {r : ℕ} (hF : F ∈ Erot1 k r) (hk : 0 < k)
    {ℓ : ℤ} (hcl : ¬ (k : ℤ) ∣ (r + ℓ)) (r₀ : ℝ) : Fm F ℓ r₀ = 0 := by
  set c : ℝ := 2 * π / k with hc
  set h : ℝ → ℂ := fun θ => slice F r₀ θ * Complex.exp (-(ℓ : ℂ) * I * θ) with hhdef
  -- `h` is `2π`-periodic.
  have hper : Function.Periodic h (2 * π) := by
    intro θ
    simp only [hhdef, slice]
    rw [show ((θ + 2 * π : ℝ) : ℂ) * I = (θ : ℂ) * I + ((2 * π : ℝ) : ℂ) * I by push_cast; ring,
      Complex.exp_add]
    rw [show ((θ + 2 * π : ℝ) : ℂ) = (θ : ℂ) + ((2 * π : ℝ) : ℂ) by push_cast; ring]
    have e1 : Complex.exp (((2 * π : ℝ) : ℂ) * I) = 1 := by
      rw [show ((2 * π : ℝ) : ℂ) * I = ((1 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
        Complex.exp_int_mul_two_pi_mul_I]
    have e2 : Complex.exp (-(ℓ : ℂ) * I * ((θ : ℂ) + ((2 * π : ℝ) : ℂ)))
        = Complex.exp (-(ℓ : ℂ) * I * (θ : ℂ)) := by
      rw [mul_add, Complex.exp_add]
      rw [show -(ℓ : ℂ) * I * ((2 * π : ℝ) : ℂ) = ((-ℓ : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
        Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [e1, mul_one, e2]
  -- The shift picks up the scalar `μ`.
  set μ : ℂ := (zeta k ^ r)⁻¹ * Complex.exp (-(ℓ : ℂ) * I * (c : ℂ)) with hμ
  have hshift : ∀ θ : ℝ, h (θ + c) = μ * h θ := by
    intro θ
    simp only [hhdef]
    rw [slice_shift hF r₀ θ]
    rw [show ((θ + c : ℝ) : ℂ) = (θ : ℂ) + (c : ℂ) by push_cast; ring, mul_add, Complex.exp_add]
    rw [hμ]; ring
  -- Integrate the shift identity over a full period.
  have hint : ∫ θ in (0 : ℝ)..2 * π, h θ = μ * ∫ θ in (0 : ℝ)..2 * π, h θ := by
    calc ∫ θ in (0 : ℝ)..2 * π, h θ
        = ∫ θ in (0 : ℝ)..2 * π, h (θ + c) := by
          rw [intervalIntegral.integral_comp_add_right h c,
            show (0 : ℝ) + c = c by ring, show (2 * π : ℝ) + c = c + 2 * π by ring]
          have hpe := hper.intervalIntegral_add_eq 0 c
          rw [zero_add] at hpe
          exact hpe
      _ = ∫ θ in (0 : ℝ)..2 * π, μ * h θ := by
          congr 1; funext θ; exact hshift θ
      _ = μ * ∫ θ in (0 : ℝ)..2 * π, h θ := intervalIntegral.integral_const_mul μ h
  -- `μ ≠ 1`, so the integral is zero.
  have hμval : μ = zeta k ^ (-(r : ℤ) - ℓ) := by
    rw [hμ]
    have hexp : Complex.exp (-(ℓ : ℂ) * I * (c : ℂ)) = zeta k ^ (-ℓ) := by
      rw [zeta, ← Complex.exp_int_mul]
      congr 1
      rw [hc]; push_cast; ring
    rw [hexp, ← zpow_natCast (zeta k) r, ← zpow_neg,
      ← zpow_add₀ (by rw [zeta]; exact Complex.exp_ne_zero _), sub_eq_add_neg]
  have hμne : μ ≠ 1 := by
    rw [hμval]
    intro hcon
    apply hcl
    have hd := (IsPrimitiveRoot.zpow_eq_one_iff_dvd (zeta_prim hk) (-(r : ℤ) - ℓ)).mp hcon
    rw [show -(r : ℤ) - ℓ = -((r : ℤ) + ℓ) by ring] at hd
    exact dvd_neg.mp hd
  have hI0 : ∫ θ in (0 : ℝ)..2 * π, h θ = 0 := by
    have h1μ : (1 : ℂ) - μ ≠ 0 := sub_ne_zero.mpr (Ne.symm hμne)
    have hfac : (1 - μ) * ∫ θ in (0 : ℝ)..2 * π, h θ = 0 := by
      rw [sub_mul, one_mul, ← hint, sub_self]
    exact (mul_eq_zero.mp hfac).resolve_left h1μ
  unfold Fm fc
  rw [show (fun θ => slice F r₀ θ * Complex.exp (-(ℓ : ℂ) * I * θ)) = h from rfl, hI0, mul_zero]

end KsIndex.FourierMode
