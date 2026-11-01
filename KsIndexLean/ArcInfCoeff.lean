module

/-
Fourier coefficients of the rescaled arc field.

The field is defined by
`fInf k r η φ = exp(i * ↑(k-r) * φ) * psiF η (k*φ)`, where `k-r` is computed
in `ℕ` before casting. Continuity and the bound `‖fInf k r η φ‖ ≤ 1` hold for
all natural `k,r` and real `η`.

For `k ≥ 1`, the normalized Fourier coefficient at `m : ℤ` vanishes unless
`(k : ℤ)` divides `s = m - ↑(k-r)`. When divisibility holds, the coefficient is
`Parseval.fc (psiF η) (s / k)`. The theorem allows arbitrary `r` and `η`; it does
not require `r < k` or positivity of the smoothing parameter.

The proof uses periodic integrals directly. Off the progression, shifting by
`2π/k` preserves the integral while multiplying it by a nontrivial phase, forcing
it to vanish. On the progression `s = k*j`, a change of variables averages over
`k` periods and recovers the coefficient of `psiF η` at `j`. The normalization is
`(2π)⁻¹` and the Fourier exponent has sign `−m`, matching the Poisson kernel's
`θ−φ` convention. No Fourier inversion is used in this coefficient calculation.
-/
public import KsIndexLean.ArcField
public import KsIndexLean.Parseval1

@[expose] public section


noncomputable section

open Real Set Filter MeasureTheory intervalIntegral Topology Complex
open KsIndex.ArcField

namespace KsIndex.ArcInfCoeff

variable {k r : ℕ} {η : ℝ}

/-! ### The boundary field and the shifted integrand -/

/-- The class-`(k−r)` boundary trace in closed form: `fInf φ = e^{i(k−r)φ}·psiF η (kφ)`. -/
def fInf (k r : ℕ) (η : ℝ) : ℝ → ℂ :=
  fun φ => Complex.exp (((k - r : ℕ) : ℂ) * ↑φ * Complex.I) * psiF η ((k : ℝ) * φ)

/-- The `s`-shifted working integrand `e^{−isφ}·psiF η (kφ)`. -/
def sMode (k : ℕ) (η : ℝ) (s : ℤ) : ℝ → ℂ :=
  fun φ => Complex.exp (-(s : ℂ) * ↑φ * Complex.I) * psiF η ((k : ℝ) * φ)

lemma norm_psiF_le_one (η θ : ℝ) : ‖psiF η θ‖ ≤ 1 := by
  rw [psiF, norm_mul, norm_vF]
  have hw := wCol_mem η θ
  have hwn : ‖((wCol η θ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw.1]
    exact hw.2
  calc hAmp θ * ‖((wCol η θ : ℝ) : ℂ)‖ ≤ 1 * 1 :=
        mul_le_mul (hAmp_le_one θ) hwn (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma continuous_fInf (k r : ℕ) (η : ℝ) : Continuous (fInf k r η) := by
  unfold fInf
  exact (Complex.continuous_exp.comp (by fun_prop)).mul
    ((continuous_psiF η).comp (continuous_const.mul continuous_id))

lemma norm_fInf_le_one (k r : ℕ) (η : ℝ) (φ : ℝ) : ‖fInf k r η φ‖ ≤ 1 := by
  unfold fInf
  rw [norm_mul]
  have he : ‖Complex.exp (((k - r : ℕ) : ℂ) * ↑φ * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_im]
  rw [he, one_mul]
  exact norm_psiF_le_one η _

lemma continuous_sMode (k : ℕ) (η : ℝ) (s : ℤ) : Continuous (sMode k η s) := by
  unfold sMode
  exact (Complex.continuous_exp.comp (by fun_prop)).mul
    ((continuous_psiF η).comp (continuous_const.mul continuous_id))

/-! ### Periodicity and the `2π/k` shift -/

/-- Integer-frequency exponentials are `2π`-periodic. -/
lemma exp_int_periodic (s : ℤ) (θ : ℝ) :
    Complex.exp (-(s : ℂ) * ↑(θ + 2 * π) * Complex.I)
      = Complex.exp (-(s : ℂ) * ↑θ * Complex.I) := by
  rw [show (-(s : ℂ) * ↑(θ + 2 * π) * Complex.I)
      = -(s : ℂ) * ↑θ * Complex.I + ((-s : ℤ) : ℂ) * (2 * ↑π * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma sMode_periodic (k : ℕ) (η : ℝ) (s : ℤ) : Function.Periodic (sMode k η s) (2 * π) := by
  intro φ
  unfold sMode
  rw [exp_int_periodic]
  congr 1
  rw [show (k : ℝ) * (φ + 2 * π) = (k : ℝ) * φ + ↑k * (2 * π) by ring]
  exact (psiF_periodic η).nat_mul k ((k : ℝ) * φ)

/-- The `2π/k` shift multiplies `sMode` by the phase `e^{−is·(2π/k)}`. -/
lemma sMode_shift (hk : 1 ≤ k) (η : ℝ) (s : ℤ) (φ : ℝ) :
    sMode k η s (φ + 2 * π / (k : ℝ))
      = Complex.exp (-(s : ℂ) * ((2 * π / (k : ℝ) : ℝ) : ℂ) * Complex.I) * sMode k η s φ := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold sMode
  rw [show ((k : ℝ) * (φ + 2 * π / (k : ℝ))) = (k : ℝ) * φ + 2 * π by field_simp]
  rw [psiF_periodic η ((k : ℝ) * φ)]
  rw [show (-(s : ℂ) * ↑(φ + 2 * π / (k : ℝ)) * Complex.I)
      = (-(s : ℂ) * ((2 * π / (k : ℝ) : ℝ) : ℂ) * Complex.I)
        + (-(s : ℂ) * ↑φ * Complex.I) by push_cast; ring,
    Complex.exp_add]
  ring

/-! ### OFF the progression: the integral vanishes -/

lemma integral_sMode_eq_zero (hk : 1 ≤ k) (η : ℝ) {s : ℤ} (hs : ¬ ((k : ℤ) ∣ s)) :
    (∫ φ in (0:ℝ)..2 * π, sMode k η s φ) = 0 := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  set ω : ℂ := Complex.exp (-(s : ℂ) * ((2 * π / (k : ℝ) : ℝ) : ℂ) * Complex.I) with hω
  -- shifting by `2π/k` preserves the integral over the period
  have hshift : (∫ φ in (0:ℝ)..2 * π, sMode k η s (φ + 2 * π / (k : ℝ)))
      = ∫ φ in (0:ℝ)..2 * π, sMode k η s φ := by
    rw [intervalIntegral.integral_comp_add_right (sMode k η s) (2 * π / (k : ℝ)), zero_add,
      show 2 * π + 2 * π / (k : ℝ) = 2 * π / (k : ℝ) + 2 * π from add_comm _ _,
      (sMode_periodic k η s).intervalIntegral_add_eq (2 * π / (k : ℝ)) 0, zero_add]
  -- but the shift also multiplies by the phase `ω`
  have hphase : (∫ φ in (0:ℝ)..2 * π, sMode k η s (φ + 2 * π / (k : ℝ)))
      = ω * ∫ φ in (0:ℝ)..2 * π, sMode k η s φ := by
    rw [show (∫ φ in (0:ℝ)..2 * π, sMode k η s (φ + 2 * π / (k : ℝ)))
        = ∫ φ in (0:ℝ)..2 * π, ω * sMode k η s φ from
      intervalIntegral.integral_congr (fun φ _ => by rw [sMode_shift hk η s φ, hω]),
      intervalIntegral.integral_const_mul]
  have hcomb : (1 - ω) * (∫ φ in (0:ℝ)..2 * π, sMode k η s φ) = 0 := by
    rw [sub_mul, one_mul, ← hphase, hshift, sub_self]
  -- `ω ≠ 1` exactly because `k ∤ s`
  have hω1 : ω ≠ 1 := by
    rw [hω]
    intro h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    have hn2 : -(s : ℂ) * ((2 * π / (k : ℝ) : ℝ) : ℂ) = (n : ℂ) * (2 * ↑π) := by
      apply mul_right_cancel₀ Complex.I_ne_zero
      rw [hn]
      ring
    have hre : -(s : ℝ) * (2 * π / (k : ℝ)) = (n : ℝ) * (2 * π) := by exact_mod_cast hn2
    have h1' : (-(s : ℝ)) * (2 * π) = ((n : ℝ) * (k : ℝ)) * (2 * π) := by
      calc (-(s : ℝ)) * (2 * π) = (-(s : ℝ) * (2 * π / (k : ℝ))) * (k : ℝ) := by field_simp
        _ = ((n : ℝ) * (2 * π)) * (k : ℝ) := by rw [hre]
        _ = ((n : ℝ) * (k : ℝ)) * (2 * π) := by ring
    have hsr : (-(s : ℝ)) = (n : ℝ) * (k : ℝ) := mul_right_cancel₀ h2π h1'
    have hsz : -s = n * (k : ℤ) := by exact_mod_cast hsr
    exact hs ⟨-n, by linear_combination -hsz⟩
  rcases mul_eq_zero.mp hcomb with h | h
  · exact absurd (by linear_combination -h : ω = 1) hω1
  · exact h

/-! ### ON the progression: the `k`-period average -/

lemma integral_sMode_mul (hk : 1 ≤ k) (η : ℝ) (j : ℤ) :
    (∫ φ in (0:ℝ)..2 * π, sMode k η ((k : ℤ) * j) φ)
      = ∫ θ in (0:ℝ)..2 * π, Complex.exp (-(j : ℂ) * ↑θ * Complex.I) * psiF η θ := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hkC : ((k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hgper : Function.Periodic
      (fun θ : ℝ => Complex.exp (-(j : ℂ) * ↑θ * Complex.I) * psiF η θ) (2 * π) := by
    intro θ
    simp only
    rw [exp_int_periodic, psiF_periodic η θ]
  have hgint : ∀ t₁ t₂ : ℝ, IntervalIntegrable
      (fun θ : ℝ => Complex.exp (-(j : ℂ) * ↑θ * Complex.I) * psiF η θ)
      MeasureSpace.volume t₁ t₂ := fun t₁ t₂ =>
    ((Complex.continuous_exp.comp (by fun_prop)).mul (continuous_psiF η)).intervalIntegrable t₁ t₂
  calc (∫ φ in (0:ℝ)..2 * π, sMode k η ((k : ℤ) * j) φ)
      = ∫ φ in (0:ℝ)..2 * π,
          (fun θ : ℝ => Complex.exp (-(j : ℂ) * ↑θ * Complex.I) * psiF η θ) ((k : ℝ) * φ) := by
        refine intervalIntegral.integral_congr (fun φ _ => ?_)
        simp only
        unfold sMode
        congr 2
        push_cast
        ring
    _ = (k : ℝ)⁻¹ • ∫ θ in (k : ℝ) * 0..(k : ℝ) * (2 * π),
          Complex.exp (-(j : ℂ) * ↑θ * Complex.I) * psiF η θ :=
        intervalIntegral.integral_comp_mul_left
          (fun θ : ℝ => Complex.exp (-(j : ℂ) * ↑θ * Complex.I) * psiF η θ) hk0
    _ = (k : ℝ)⁻¹ • ((k : ℤ) • ∫ θ in (0:ℝ)..2 * π,
          Complex.exp (-(j : ℂ) * ↑θ * Complex.I) * psiF η θ) := by
        congr 1
        rw [mul_zero, show (k : ℝ) * (2 * π) = 0 + (k : ℤ) • (2 * π : ℝ) from by
          rw [zero_add, zsmul_eq_mul]; push_cast; ring]
        rw [hgper.intervalIntegral_add_zsmul_eq (k : ℤ) 0 hgint, zero_add]
    _ = ∫ θ in (0:ℝ)..2 * π, Complex.exp (-(j : ℂ) * ↑θ * Complex.I) * psiF η θ := by
        rw [zsmul_eq_mul, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
          Int.cast_natCast, ← mul_assoc, inv_mul_cancel₀ hkC, one_mul]

/-- Bridge to the arc coefficient: `(2π)⁻¹·∫ e^{−ijθ}·psiF = fc (psiF η) j`. -/
lemma integral_g_eq_fc (η : ℝ) (j : ℤ) :
    ((2 * π)⁻¹ : ℂ) * (∫ θ in (0:ℝ)..2 * π, Complex.exp (-(j : ℂ) * ↑θ * Complex.I) * psiF η θ)
      = Parseval.fc (psiF η) j := by
  simp only [Parseval.fc]
  rw [show (∫ θ in (0:ℝ)..2 * π, Complex.exp (-(j : ℂ) * ↑θ * Complex.I) * psiF η θ)
      = ∫ θ in (0:ℝ)..2 * π, psiF η θ * Complex.exp (-(j : ℂ) * Complex.I * ↑θ) from
    intervalIntegral.integral_congr (fun θ _ => by
      rw [show (-(j : ℂ) * ↑θ * Complex.I) = -(j : ℂ) * Complex.I * ↑θ from by ring]
      ring)]
  congr 1
  norm_cast

/-! ### The coefficient theorem -/

/-- The Fourier coefficients of `fInf` vanish off the progression `m ≡ ↑(k-r) (mod k)`
and equal the corresponding arc coefficients on it. Here `k-r` is natural subtraction. -/
theorem coeff_fInf_eq (hk : 1 ≤ k) (η : ℝ) (m : ℤ) :
    ((2 * π)⁻¹ : ℂ)
        * (∫ φ in (0:ℝ)..2 * π, Complex.exp (-(m : ℂ) * ↑φ * Complex.I) * fInf k r η φ)
      = if (k : ℤ) ∣ (m - ((k - r : ℕ) : ℤ))
          then Parseval.fc (psiF η) ((m - ((k - r : ℕ) : ℤ)) / (k : ℤ)) else 0 := by
  have hkZ : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
  have hred : (∫ φ in (0:ℝ)..2 * π, Complex.exp (-(m : ℂ) * ↑φ * Complex.I) * fInf k r η φ)
      = ∫ φ in (0:ℝ)..2 * π, sMode k η (m - ((k - r : ℕ) : ℤ)) φ := by
    refine intervalIntegral.integral_congr (fun φ _ => ?_)
    unfold fInf sMode
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hred]
  by_cases hdvd : (k : ℤ) ∣ (m - ((k - r : ℕ) : ℤ))
  · rw [if_pos hdvd]
    obtain ⟨j, hj⟩ := hdvd
    rw [hj, Int.mul_ediv_cancel_left j hkZ, integral_sMode_mul hk η j]
    exact integral_g_eq_fc η j
  · rw [if_neg hdvd, integral_sMode_eq_zero hk η hdvd, mul_zero]

end KsIndex.ArcInfCoeff
