module

/-
KsIndexLean — SquareWaveCoefficients: the base square-wave Fourier coefficients.

The complex Fourier coefficients of `sgn(cos θ)` on `[0, 2π]` in Mathlib's `fourierCoeffOn`
normalization — the one irreducible analytic link for the k=3 arbitrary-m seam↔mulA intertwiner
(`PaperSlitIntertwiner`). Self-contained (Mathlib only).

Proof provenance: Aristotle (Harmonic), job `6349eacf`, supplied the two
principal proofs. Astra ported them to Lean 4.34.0-rc2, replacing the `sqE_int`
antiderivative argument with complex differentiation and
`comp_ofReal`/`div_const` to resolve a scalar-instance elaboration change.
Kai integrated and independently checked the port.
-/
public import Mathlib.Analysis.Fourier.AddCircle

@[expose] public section


open Real
noncomputable section
namespace KsIndex.Trace

section SquareWaveHelpers
open MeasureTheory Interval

private noncomputable def sqE (n : ℤ) (x : ℝ) : ℂ := Complex.exp ((-(n : ℂ) * Complex.I) * x)

private lemma sqE_cont (n : ℤ) : Continuous (sqE n) := by
  unfold sqE; fun_prop

private lemma sq_ae1 (n : ℤ) : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι 0 (π/2) →
    sqE n x * (if 0 ≤ Real.cos x then (1 : ℂ) else -1) = sqE n x := by
  refine ae_of_all _ fun x hx => ?_
  rw [Set.uIoc_of_le (by positivity)] at hx
  have : 0 ≤ Real.cos x :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hx.1, pi_pos]) hx.2
  simp [this]

private lemma sq_ae3 (n : ℤ) : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι (3*π/2) (2*π) →
    sqE n x * (if 0 ≤ Real.cos x then (1 : ℂ) else -1) = sqE n x := by
  refine ae_of_all _ fun x hx => ?_
  rw [Set.uIoc_of_le (by linarith [pi_pos])] at hx
  have : 0 ≤ Real.cos x := by
    rw [← Real.cos_sub_two_pi]
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hx.1])
      (by linarith [hx.2, pi_pos])
  simp [this]

private lemma sq_ae2 (n : ℤ) : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι (π/2) (3*π/2) →
    sqE n x * (if 0 ≤ Real.cos x then (1 : ℂ) else -1) = -sqE n x := by
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 3*π/2 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with x hx hmem
  rw [Set.uIoc_of_le (by linarith [pi_pos])] at hmem
  have : Real.cos x < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt hmem.1 (by
      rcases lt_or_eq_of_le hmem.2 with h | h
      · linarith
      · exact absurd h hx)
  simp [not_le.mpr this]

private lemma sq_ii {n : ℤ} {a b : ℝ} {h : ℝ → ℂ} (hc : Continuous h)
    (hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι a b →
      sqE n x * (if 0 ≤ Real.cos x then (1 : ℂ) else -1) = h x) :
    IntervalIntegrable (fun x => sqE n x * (if 0 ≤ Real.cos x then (1 : ℂ) else -1))
      volume a b := by
  refine (hc.intervalIntegrable a b).congr_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hae] with x hx hm using (hx hm).symm

private lemma sq_split (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos
        (fun θ : ℝ => if 0 ≤ Real.cos θ then (1 : ℂ) else -1) n
      = (1 / (2 * π) : ℂ) * ((∫ x in (0:ℝ)..(π/2), sqE n x) - (∫ x in (π/2)..(3*π/2), sqE n x)
          + ∫ x in (3*π/2)..(2*π), sqE n x) := by
  rw [fourierCoeffOn_eq_integral]
  have h1 : ∀ x : ℝ, fourier (-n) (x : AddCircle (2 * π - 0))
        • (if 0 ≤ Real.cos x then (1 : ℂ) else -1)
      = sqE n x * (if 0 ≤ Real.cos x then (1 : ℂ) else -1) := by
    intro x
    rw [fourier_coe_apply, smul_eq_mul, sqE]
    congr 2
    push_cast
    field_simp
    ring
  simp_rw [h1]
  have i1 := sq_ii (sqE_cont n) (sq_ae1 n)
  have i2 := sq_ii (sqE_cont n).neg (sq_ae2 n)
  have i3 := sq_ii (sqE_cont n) (sq_ae3 n)
  rw [sub_zero, ← intervalIntegral.integral_add_adjacent_intervals (b := 3*π/2) (i1.trans i2) i3,
    ← intervalIntegral.integral_add_adjacent_intervals (b := π/2) i1 i2,
    intervalIntegral.integral_congr_ae (sq_ae1 n), intervalIntegral.integral_congr_ae (sq_ae2 n),
    intervalIntegral.integral_congr_ae (sq_ae3 n), intervalIntegral.integral_neg, Complex.real_smul]
  push_cast
  ring

private lemma sqE_int (n : ℤ) (hn : n ≠ 0) (a b : ℝ) :
    ∫ x in a..b, sqE n x = (sqE n b - sqE n a) / (-(n : ℂ) * Complex.I) := by
  have hc : (-(n : ℂ) * Complex.I) ≠ 0 := by simp [hn]
  have D : ∀ x : ℝ, HasDerivAt (fun y : ℝ => sqE n y / (-(n : ℂ) * Complex.I)) (sqE n x) x := by
    intro x
    have h := ((Complex.hasDerivAt_exp ((-(n : ℂ) * Complex.I) * (x : ℂ))).comp
      (x : ℂ) ((hasDerivAt_id (x : ℂ)).const_mul (-(n : ℂ) * Complex.I))).comp_ofReal
    have hd := h.div_const (-(n : ℂ) * Complex.I)
    simpa only [sqE, Function.comp_apply, id_eq, mul_one, mul_div_cancel_right₀ _ hc] using hd
  rw [intervalIntegral.integral_deriv_eq_sub' _ (funext fun x => (D x).deriv)
    (fun x _ => (D x).differentiableAt) (sqE_cont n).continuousOn]
  ring

private lemma sqE_zero (n : ℤ) : sqE n 0 = 1 := by simp [sqE]

private lemma sqE_two_pi (n : ℤ) : sqE n (2 * π) = 1 := by
  have := Complex.exp_int_mul_two_pi_mul_I (-n)
  rw [sqE, ← this]; congr 1; push_cast; ring

private lemma sqE_pi_div_two (n : ℤ) : sqE n (π / 2) = (-Complex.I) ^ n := by
  rw [sqE, show (-(n : ℂ) * Complex.I) * ((π / 2 : ℝ) : ℂ) = n * (-(π / 2 * Complex.I)) by
    push_cast; ring, Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_div_two_mul_I,
    Complex.inv_I]

private lemma sqE_three_pi_div_two (n : ℤ) : sqE n (3 * π / 2) = Complex.I ^ n := by
  have h : Complex.exp (-(3 * π / 2 * Complex.I)) = Complex.I := by
    rw [show -(3 * π / 2 * Complex.I) = π / 2 * Complex.I + (-1 : ℤ) * (2 * π * Complex.I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
      Complex.exp_pi_div_two_mul_I]
  rw [sqE, show (-(n : ℂ) * Complex.I) * ((3 * π / 2 : ℝ) : ℂ) = n * (-(3 * π / 2 * Complex.I)) by
    push_cast; ring, Complex.exp_int_mul, h]

private lemma sq_formula (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn Real.two_pi_pos
        (fun θ : ℝ => if 0 ≤ Real.cos θ then (1 : ℂ) else -1) n
      = (1 / (2 * π) : ℂ)
          * ((2 * (-Complex.I) ^ n - 2 * Complex.I ^ n) / (-(n : ℂ) * Complex.I)) := by
  rw [sq_split, sqE_int n hn, sqE_int n hn, sqE_int n hn, sqE_zero, sqE_two_pi, sqE_pi_div_two,
    sqE_three_pi_div_two]
  congr 1
  ring

end SquareWaveHelpers

/-- (2k+1)-th Fourier coefficient of `sgn(cos θ)` on `[0,2π]` is `(2/π)(-1)^k/(2k+1)`. -/
theorem squareWave_fourierCoeffOn_odd (k : ℤ) :
    fourierCoeffOn Real.two_pi_pos
        (fun θ : ℝ => if 0 ≤ Real.cos θ then (1 : ℂ) else -1) (2 * k + 1)
      = ((2 / π * (-1) ^ k / (2 * (k : ℝ) + 1) : ℝ) : ℂ) := by
  have hn : (2 * k + 1 : ℤ) ≠ 0 := by omega
  have hnC : (2 * (k : ℂ) + 1) ≠ 0 := by exact_mod_cast hn
  rw [sq_formula _ hn]
  have h1 : Complex.I ^ (2 * k + 1) = (-1) ^ k * Complex.I := by
    rw [zpow_add₀ Complex.I_ne_zero, zpow_mul, zpow_two, Complex.I_mul_I, zpow_one]
  have h2 : (-Complex.I) ^ (2 * k + 1) = -((-1) ^ k * Complex.I) := by
    rw [zpow_add₀ (neg_ne_zero.mpr Complex.I_ne_zero), zpow_mul, zpow_two, neg_mul_neg,
      Complex.I_mul_I, zpow_one, mul_neg]
  rw [h1, h2]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring_nf

/-- Even-frequency Fourier coefficients of `sgn(cos θ)` on `[0,2π]` vanish. -/
theorem squareWave_fourierCoeffOn_even (k : ℤ) :
    fourierCoeffOn Real.two_pi_pos
        (fun θ : ℝ => if 0 ≤ Real.cos θ then (1 : ℂ) else -1) (2 * k) = 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [sq_split]
    simp only [mul_zero, Int.cast_zero, sqE, neg_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, Complex.real_smul]
    push_cast
    field_simp
    ring
  · have hn : (2 * k : ℤ) ≠ 0 := by omega
    rw [sq_formula _ hn]
    have h1 : Complex.I ^ (2 * k) = (-1) ^ k := by
      rw [zpow_mul, zpow_two, Complex.I_mul_I]
    have h2 : (-Complex.I) ^ (2 * k) = (-1) ^ k := by
      rw [zpow_mul, zpow_two, neg_mul_neg, Complex.I_mul_I]
    rw [h1, h2]
    simp

end KsIndex.Trace
