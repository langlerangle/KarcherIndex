module

/-
Normalized radial profiles for the Jacobi extension.

For `k ≥ 2` and nonzero angular frequency `ℓ ≥ 1`, the profile
`phiExt k ℓ r = uRad k ℓ r / ℓ` has boundary value one and vanishes at the
origin. Its derivative `phiExtD` is defined at every radius, including zero.

The profile has zero Wronskian with the radial mode, so the remainder in
`qMode_eq` vanishes. Consequently `phiExt_energy` identifies its radial
Jacobi energy with the Dirichlet-to-Neumann symbol
`sigma k ℓ = (ℓ² - (k - 1)²) / ℓ`. The complex version `phiExtC_energy`
multiplies this energy by the squared norm of the boundary coefficient.

These are one-dimensional radial identities. Angular orthogonality,
two-dimensional integration, and convergence of the full extension series
are established separately.
-/
public import KsIndexLean.RadialMode

@[expose] public section


noncomputable section

namespace KsIndex.JacobiExtension

open KsIndex.Radial Set intervalIntegral MeasureTheory

variable {k ℓ : ℕ}

/-! ### An everywhere-valid derivative of the mode `uRad` -/

/-- The derivative of `uRad k ℓ = r^ℓ · gRad k ℓ` by the product rule, valid at *every* `r`
(including the centre `r = 0`), unlike `uD` which divides by `r`. -/
def uD2 (k ℓ : ℕ) (r : ℝ) : ℝ := (ℓ : ℝ) * r ^ (ℓ - 1) * gRad k ℓ r + r ^ ℓ * gD k r

lemma uRad_hasDerivAt' (hk : 2 ≤ k) (ℓ : ℕ) (r : ℝ) :
    HasDerivAt (uRad k ℓ) (uD2 k ℓ r) r := by
  have h : HasDerivAt (fun r => r ^ ℓ * gRad k ℓ r)
      ((ℓ : ℝ) * r ^ (ℓ - 1) * gRad k ℓ r + r ^ ℓ * gD k r) r :=
    (hasDerivAt_pow ℓ r).mul (gRad_hasDerivAt hk ℓ r)
  exact h

lemma gRad_continuous (hk : 2 ≤ k) (ℓ : ℕ) : Continuous (gRad k ℓ) :=
  continuous_iff_continuousAt.mpr fun r => (gRad_hasDerivAt hk ℓ r).continuousAt

lemma gD_continuous (hk : 2 ≤ k) : Continuous (gD k) :=
  continuous_iff_continuousAt.mpr fun r => (gD_hasDerivAt hk r).continuousAt

lemma uD2_continuous (hk : 2 ≤ k) (ℓ : ℕ) : Continuous (uD2 k ℓ) := by
  have := gRad_continuous hk ℓ
  have := gD_continuous hk
  unfold uD2
  fun_prop

lemma uRad_zero (hℓ : 1 ≤ ℓ) : uRad k ℓ 0 = 0 := by
  rw [uRad, zero_pow (by omega : ℓ ≠ 0), zero_mul]

/-! ### The Wronskian of the mode vanishes -/

/-- `Wg` of the mode with its own derivative vanishes identically (the mode is a solution). -/
lemma Wg_uRad (hℓ : 1 ≤ ℓ) (r : ℝ) : Wg k ℓ (uRad k ℓ) (uD2 k ℓ) r = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Wg, uRad, uD2, Nat.add_sub_cancel, pow_succ]
  push_cast
  ring

/-! ### The normalized radial extension profile -/

/-- The radial profile of the Jacobi extension, normalized to boundary value `1`:
`φ_{k,ℓ}(r) = uRad k ℓ r / ℓ`. -/
def phiExt (k ℓ : ℕ) (r : ℝ) : ℝ := uRad k ℓ r / (ℓ : ℝ)

/-- Its derivative. -/
def phiExtD (k ℓ : ℕ) (r : ℝ) : ℝ := uD2 k ℓ r / (ℓ : ℝ)

lemma phiExt_hasDerivAt (hk : 2 ≤ k) (ℓ : ℕ) (r : ℝ) :
    HasDerivAt (phiExt k ℓ) (phiExtD k ℓ r) r :=
  (uRad_hasDerivAt' hk ℓ r).div_const _

lemma phiExtD_continuous (hk : 2 ≤ k) (ℓ : ℕ) : Continuous (phiExtD k ℓ) :=
  (uD2_continuous hk ℓ).div_const _

lemma phiExt_zero (hℓ : 1 ≤ ℓ) : phiExt k ℓ 0 = 0 := by
  rw [phiExt, uRad_zero hℓ, zero_div]

lemma phiExt_one (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) : phiExt k ℓ 1 = 1 := by
  rw [phiExt, uRad_one hk]
  exact div_self (by exact_mod_cast (by omega : ℓ ≠ 0))

/-- The extension's Wronskian is `1/ℓ` times the mode's, hence also zero. -/
lemma Wg_phiExt (r : ℝ) :
    Wg k ℓ (phiExt k ℓ) (phiExtD k ℓ) r = Wg k ℓ (uRad k ℓ) (uD2 k ℓ) r / (ℓ : ℝ) := by
  simp only [Wg, phiExt, phiExtD]
  ring

/-- The nonnegative remainder vanishes for the extension: it realizes equality in `qMode_eq`. -/
lemma Rm_phiExt (hℓ : 1 ≤ ℓ) (r : ℝ) : Rm k ℓ (phiExt k ℓ) (phiExtD k ℓ) r = 0 := by
  rw [Rm, Wg_phiExt, Wg_uRad hℓ]
  simp

/-! ### The per-mode extension energy equals the DtN symbol -/

/-- **The Jacobi energy of the normalized extension is exactly the DtN symbol**:
`∫₀¹ (r φ'² + ℓ² φ²/r − r V φ²) dr = σ_k(ℓ)`.  (Equality in the ground-state identity, `Rm ≡ 0`.) -/
theorem phiExt_energy (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) :
    ∫ r in (0:ℝ)..1, lhs k ℓ (phiExt k ℓ) (phiExtD k ℓ) r = sigma k ℓ := by
  have hf : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt (phiExt k ℓ) (phiExtD k ℓ r) r :=
    fun r _ => phiExt_hasDerivAt hk ℓ r
  have hf' : ContinuousOn (phiExtD k ℓ) (Icc 0 1) := (phiExtD_continuous hk ℓ).continuousOn
  rw [qMode_eq hk hℓ hf hf' (phiExt_zero hℓ)]
  have hRm : ∫ r in (0:ℝ)..1, Rm k ℓ (phiExt k ℓ) (phiExtD k ℓ) r = 0 := by
    simp only [Rm_phiExt hℓ, intervalIntegral.integral_zero]
  rw [hRm, phiExt_one hk hℓ]
  ring

/-! ### Complex per-mode contribution -/

/-- The complex density of `c · φ` (real `φ`) is `‖c‖²` times the real density of `φ`. -/
lemma lhsC_scale (c : ℂ) (φ φ' : ℝ → ℝ) (r : ℝ) :
    lhsC k ℓ (fun r => c * (φ r : ℂ)) (fun r => c * (φ' r : ℂ)) r = ‖c‖ ^ 2 * lhs k ℓ φ φ' r := by
  simp only [lhsC, lhs, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- **Per-mode contribution of a boundary coefficient `c`**:
`∫₀¹ lhsC(c·φ) = σ_k(ℓ) · ‖c‖²`. -/
theorem phiExtC_energy (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) (c : ℂ) :
    ∫ r in (0:ℝ)..1,
        lhsC k ℓ (fun r => c * (phiExt k ℓ r : ℂ)) (fun r => c * (phiExtD k ℓ r : ℂ)) r
      = sigma k ℓ * ‖c‖ ^ 2 := by
  simp_rw [lhsC_scale]
  rw [intervalIntegral.integral_const_mul, phiExt_energy hk hℓ]
  ring

end KsIndex.JacobiExtension
