module

/-
# Disk ground-state energy and a radial cross-term identity

For k >= 2, the radial ground state `groundC k` has zero disk Jacobi
energy. Its Fourier coefficients and their radial derivatives vanish
outside angular mode zero, whose energy is zero by the radial mode identity.

For a real profile with a derivative continuous on `[0,1]`, `cross_ftc`
evaluates the radial cross term as `gD k 1 * u 1`. The mode ODE identifies
the integrand with the derivative of `r * gD k r * u r`; the endpoint at
zero contributes nothing. `cross_ftc'` substitutes `gD k 1 = -(kap k)^2`.
-/
public import KsIndexLean.PiAssembly
public import KsIndexLean.SlitCutoff

@[expose] public section


noncomputable section

open Complex MeasureTheory Set Filter intervalIntegral
open KsIndex.Parseval KsIndex.FourierMode KsIndex.Radial KsIndex.Surface KsIndex.SurfaceForm
  KsIndex.SingleDiskBridge KsIndex.PiAssembly
open scoped ContDiff

namespace KsIndex.SingleDisk

variable {k : ℕ}

/-! ### The ground state as a complex-valued function on `ℂ` -/

/-- The ground state `gRad k 0 ∘ ‖·‖` as a globally smooth `ℂ`-valued function. -/
def groundC (k : ℕ) (w : ℂ) : ℂ := ((groundR k w : ℝ) : ℂ)

lemma contDiff_groundC (k : ℕ) : ContDiff ℝ ∞ (groundC k) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_groundR k)

lemma one_le_infty : (1 : WithTop ℕ∞) ≤ ∞ :=
  le_trans (by norm_num) KsIndex.Surface.two_le_infty

/-- `gRad k 0` is even. -/
lemma gRad_zero_abs (r : ℝ) : gRad k 0 |r| = gRad k 0 r := by
  rw [gRad, gRad, show 2 * k - 2 = 2 * (k - 1) by omega, pow_mul, pow_mul, sq_abs]

/-! ### The modes of a radial function -/

/-- Only the `ℓ = 0` angular mode of the ground state survives. -/
lemma Fm_groundC (hk : 1 ≤ k) (ℓ : ℤ) (r : ℝ) :
    Fm (groundC k) ℓ r = if ℓ = 0 then ((gRad k 0 r : ℝ) : ℂ) else 0 := by
  unfold Fm
  have hs : slice (groundC k) r = fun _ => ((gRad k 0 r : ℝ) : ℂ) := by
    funext θ
    simp only [slice, groundC]
    congr 1
    rw [groundR_eq hk, norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs,
      gRad_zero_abs]
  rw [hs]
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · rw [if_pos rfl]
    unfold fc
    simp only [Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul, ← mul_assoc,
      ← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0),
      Complex.ofReal_one, one_mul]
  · rw [if_neg hℓ]
    unfold fc
    rw [intervalIntegral.integral_const_mul, integral_exp_period ℓ hℓ, mul_zero, mul_zero]

/-- The radial derivative of the modes: only `ℓ = 0` survives, with value `gD`. -/
lemma FmD_groundC (hk2 : 2 ≤ k) (ℓ : ℤ) (r : ℝ) :
    FmD (groundC k) ℓ r = if ℓ = 0 then ((gD k r : ℝ) : ℂ) else 0 := by
  have hk1 : 1 ≤ k := by omega
  have hG1 : ContDiff ℝ 1 (groundC k) := (contDiff_groundC k).of_le one_le_infty
  have hFm := Fm_hasDerivAt hG1 ℓ r
  have hfun : Fm (groundC k) ℓ = fun s => if ℓ = 0 then ((gRad k 0 s : ℝ) : ℂ) else 0 :=
    funext fun s => Fm_groundC hk1 ℓ s
  rw [hfun] at hFm
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · simp only [if_pos] at hFm ⊢
    have hexp : HasDerivAt (fun s => ((gRad k 0 s : ℝ) : ℂ)) ((gD k r : ℝ) : ℂ) r := by
      have h := (Complex.ofRealCLM.hasFDerivAt (x := gRad k 0 r)).comp_hasDerivAt r
        (gRad_hasDerivAt hk2 0 r)
      simpa [Function.comp_def] using h
    exact hFm.unique hexp
  · simp only [if_neg hℓ] at hFm ⊢
    exact hFm.unique (hasDerivAt_const r 0)

/-! ### The disk energy of the ground state -/

/-- **The ground state has zero disk energy**: `Qd k (groundC k) = 0`. -/
theorem Qd_ground_zero (hk2 : 2 ≤ k) : Qd k (groundC k) = 0 := by
  have hk1 : 1 ≤ k := by omega
  have hG1 : ContDiff ℝ 1 (groundC k) := (contDiff_groundC k).of_le one_le_infty
  rw [Qd_eq_tsum hG1 hk2]
  have hterm : ∀ ℓ : ℤ, ℓ ≠ 0 →
      (∫ s in (0 : ℝ)..1,
        lhsC k ℓ.natAbs (Fm (groundC k) ℓ) (FmD (groundC k) ℓ) s) = 0 := by
    intro ℓ hℓ
    have hz : ∀ s, lhsC k ℓ.natAbs (Fm (groundC k) ℓ) (FmD (groundC k) ℓ) s = 0 := by
      intro s
      rw [lhsC, Fm_groundC hk1, FmD_groundC hk2, if_neg hℓ, if_neg hℓ]
      simp
    simp only [hz]
    simp
  rw [tsum_eq_single 0 hterm]
  have h0 : (∫ s in (0 : ℝ)..1,
      lhsC k (0 : ℤ).natAbs (Fm (groundC k) 0) (FmD (groundC k) 0) s)
      = ∫ s in (0 : ℝ)..1, lhs k 0 (gRad k 0) (gD k) s := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [lhsC, lhs, Int.natAbs_zero, Fm_groundC hk1, FmD_groundC hk2, if_pos rfl, if_pos rfl,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  rw [h0, qMode_zero_uRad hk2, mul_zero]

/-! ### The 1-D cross-term FTC -/

lemma uD_zero_eq : uD k 0 = gD k := by
  funext r
  simp [uD]

/-- The `ℓ = 0` mode ODE, in the form used by the cross term: `(r g')' = −r V g`. -/
lemma rgD_hasDerivAt (hk2 : 2 ≤ k) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun r => r * gD k r) (-(x * Vrad k x * gRad k 0 x)) x := by
  have h := uRad_ode hk2 0 hx
  simp only [uD_zero_eq, Nat.cast_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_mul, zero_div, zero_sub, uRad, pow_zero, one_mul] at h
  exact h

/-- **The cross-term FTC**: `∫_0^1 (r g' u' − r V g u) dr = g'(1) u(1)` for any `C¹` profile
`u` — the integrand is exactly `d/dr [r g' u]` by the mode ODE; no Picone remainder. -/
theorem cross_ftc (hk2 : 2 ≤ k) {u u' : ℝ → ℝ}
    (hu : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivAt u (u' r) r) (hu' : ContinuousOn u' (Icc 0 1)) :
    ∫ r in (0 : ℝ)..1, (r * gD k r * u' r - r * Vrad k r * gRad k 0 r * u r)
      = gD k 1 * u 1 := by
  have hucont : ContinuousOn u (Icc 0 1) :=
    fun r hr => (hu r hr).continuousAt.continuousWithinAt
  have hgDcont : Continuous (gD k) := by
    have : ∀ r, HasDerivAt (gD k) (gDD k r) r := fun r => gD_hasDerivAt hk2 r
    exact continuous_iff_continuousAt.mpr fun r => (this r).continuousAt
  have hgcont : Continuous (gRad k 0) := by
    have : ∀ r, HasDerivAt (gRad k 0) (gD k r) r := fun r => gRad_hasDerivAt hk2 0 r
    exact continuous_iff_continuousAt.mpr fun r => (this r).continuousAt
  -- the primitive P r = r * gD r * u r
  set P : ℝ → ℝ := fun r => r * gD k r * u r with hP
  have hPcont : ContinuousOn P (Icc 0 1) :=
    ((continuousOn_id.mul hgDcont.continuousOn).mul hucont)
  have hPderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt P
      (x * gD k x * u' x - x * Vrad k x * gRad k 0 x * u x) x := by
    intro x hx
    have h1 := (rgD_hasDerivAt hk2 hx.1.ne').mul (hu x (Ioo_subset_Icc_self hx))
    exact h1.congr_deriv (by ring)
  have hint : IntervalIntegrable
      (fun r => r * gD k r * u' r - r * Vrad k r * gRad k 0 r * u r) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    exact ((continuousOn_id.mul hgDcont.continuousOn).mul hu').sub
      ((((continuousOn_id.mul (continuous_Vrad k).continuousOn).mul
        hgcont.continuousOn)).mul hucont)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one hPcont
    (fun x hx => (hPderiv x hx).hasDerivWithinAt) hint
  rw [hFTC]
  simp only [hP]
  ring

/-- The boundary value in closed form: `g'(1) = −κ²`, so the cross pairing is `−κ² u(1)`. -/
theorem cross_ftc' (hk2 : 2 ≤ k) {u u' : ℝ → ℝ}
    (hu : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivAt u (u' r) r) (hu' : ContinuousOn u' (Icc 0 1)) :
    ∫ r in (0 : ℝ)..1, (r * gD k r * u' r - r * Vrad k r * gRad k 0 r * u r)
      = -(kap k ^ 2) * u 1 := by
  rw [cross_ftc hk2 hu hu', gD_one hk2]

end KsIndex.SingleDisk
