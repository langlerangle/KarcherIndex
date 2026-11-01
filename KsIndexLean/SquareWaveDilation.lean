module

/-
KsIndexLean — SquareWaveDilation: the `φ=3θ` dilation of the square-wave Fourier coefficients.

Reduces `fourierCoeffOn (sgn(cos 3θ))` to the base `fourierCoeffOn (sgn(cos θ))`
(`SquareWaveCoefficients`): the `3e`-th coefficient equals the base `e`-th coefficient, and
coefficients off multiples of 3 vanish (period `2π/3`). Together with the base coefficients this
fully determines `circleFourierCoeff sigmaField` (used by the seam↔mulA intertwiner).
Self-contained (Mathlib only).

Proof provenance: Aristotle (Harmonic), job `4438640c`, supplied both proofs.
Astra checked the returned source unchanged in Lean 4.34.0-rc2; Kai integrated
and independently checked it.
-/
public import Mathlib.Analysis.Fourier.AddCircle

@[expose] public section


open Real
noncomputable section
namespace KsIndex.Trace

private lemma sgnCos3_coeff_eq_integral (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn Real.two_pi_pos f n =
      (1 / (2 * π) : ℝ) • ∫ x in (0:ℝ)..2 * π, Complex.exp (-(n:ℂ) * x * Complex.I) * f x := by
  rw [fourierCoeffOn_eq_integral, sub_zero]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [fourier_coe_apply, smul_eq_mul]
  congr 2
  have h : (π : ℂ) ≠ 0 := by exact_mod_cast pi_pos.ne'
  push_cast
  field_simp

private lemma sgnCos3_exp_two_pi (n : ℤ) : Complex.exp (-(n:ℂ) * (2 * π : ℝ) * Complex.I) = 1 :=
  Complex.exp_eq_one_iff.2 ⟨-n, by push_cast; ring⟩

private lemma sgnCos3_intervalIntegrable (c : ℝ) (n : ℤ) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Complex.exp (-(n:ℂ) * x * Complex.I) *
      (if 0 ≤ Real.cos (c * x) then (1 : ℂ) else -1)) MeasureTheory.volume a b := by
  have hs : Measurable (fun x : ℝ => if 0 ≤ Real.cos (c * x) then (1 : ℂ) else -1) :=
    Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const
      measurable_const
  rw [intervalIntegrable_iff]
  have hc : MeasureTheory.IntegrableOn (fun x : ℝ => Complex.exp (-(n:ℂ) * x * Complex.I))
      (Set.uIoc a b) := ((by fun_prop : Continuous fun x : ℝ =>
        Complex.exp (-(n:ℂ) * x * Complex.I)).intervalIntegrable a b).def'
  have := hc.bdd_mul (c := 1) hs.aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun x => by split_ifs <;> simp)
  rw [show (fun x : ℝ => Complex.exp (-(n:ℂ) * x * Complex.I) *
      (if 0 ≤ Real.cos (c * x) then (1 : ℂ) else -1)) = fun x : ℝ =>
      (if 0 ≤ Real.cos (c * x) then (1 : ℂ) else -1) * Complex.exp (-(n:ℂ) * x * Complex.I) from
    funext fun _ => mul_comm _ _]
  exact this

/-- 3e-th coeff of `sgn(cos 3θ)` on `[0,2π]` = e-th coeff of the base `sgn(cos θ)`. -/
theorem sgnCos3_fourierCoeffOn_mul_three (e : ℤ) :
    fourierCoeffOn Real.two_pi_pos
        (fun θ : ℝ => if 0 ≤ Real.cos (3 * θ) then (1 : ℂ) else -1) (3 * e)
      = fourierCoeffOn Real.two_pi_pos
          (fun θ : ℝ => if 0 ≤ Real.cos θ then (1 : ℂ) else -1) e := by
  rw [sgnCos3_coeff_eq_integral, sgnCos3_coeff_eq_integral]
  congr 1
  set f : ℝ → ℂ := fun x => Complex.exp (-(e:ℂ) * x * Complex.I) *
    (if 0 ≤ Real.cos x then (1 : ℂ) else -1) with hf
  have hper : Function.Periodic f (2 * π) := by
    intro x
    simp only [hf, Real.cos_add_two_pi]
    congr 1
    rw [show -(e:ℂ) * ((x + 2 * π : ℝ) : ℂ) * Complex.I
        = -(e:ℂ) * (x : ℂ) * Complex.I + -(e:ℂ) * (2 * π : ℝ) * Complex.I by push_cast; ring,
      Complex.exp_add, sgnCos3_exp_two_pi, mul_one]
  have hint : ∀ a b, IntervalIntegrable f MeasureTheory.volume a b := by
    intro a b
    simpa [hf, one_mul] using sgnCos3_intervalIntegrable 1 e a b
  have h1 : (∫ x in (0:ℝ)..2 * π, Complex.exp (-((3 * e : ℤ) : ℂ) * x * Complex.I) *
      (if 0 ≤ Real.cos (3 * x) then (1 : ℂ) else -1)) = ∫ x in (0:ℝ)..2 * π, f (3 * x) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hf]
    push_cast
    ring_nf
  rw [h1, intervalIntegral.integral_comp_mul_left f (by norm_num : (3:ℝ) ≠ 0)]
  have h2 := hper.intervalIntegral_add_zsmul_eq 3 0 hint
  rw [show (3:ℝ) * 0 = 0 by ring, show (3:ℝ) * (2 * π) = 0 + (3:ℤ) • (2 * π) by
    rw [zero_add, zsmul_eq_mul]; push_cast; ring, h2, zero_add, ← Int.cast_smul_eq_zsmul ℝ,
    smul_smul]
  norm_num

/-- d-th coeff of `sgn(cos 3θ)` vanishes when `3 ∤ d`. -/
theorem sgnCos3_fourierCoeffOn_not_dvd (d : ℤ) (hd : ¬ (3 : ℤ) ∣ d) :
    fourierCoeffOn Real.two_pi_pos
        (fun θ : ℝ => if 0 ≤ Real.cos (3 * θ) then (1 : ℂ) else -1) d = 0 := by
  rw [sgnCos3_coeff_eq_integral]
  set F : ℝ → ℂ := fun x => Complex.exp (-(d:ℂ) * x * Complex.I) *
    (if 0 ≤ Real.cos (3 * x) then (1 : ℂ) else -1) with hF
  have hper : Function.Periodic F (2 * π) := by
    intro x
    have hc : Real.cos (3 * (x + 2 * π)) = Real.cos (3 * x) := by
      rw [show 3 * (x + 2 * π) = 3 * x + (3 : ℕ) * (2 * π) by push_cast; ring]
      exact Real.cos_add_nat_mul_two_pi _ _
    simp only [hF, hc]
    congr 1
    rw [show -(d:ℂ) * ((x + 2 * π : ℝ) : ℂ) * Complex.I
        = -(d:ℂ) * (x : ℂ) * Complex.I + -(d:ℂ) * (2 * π : ℝ) * Complex.I by push_cast; ring,
      Complex.exp_add, sgnCos3_exp_two_pi, mul_one]
  set ω : ℂ := Complex.exp (-(d:ℂ) * (2 * π / 3 : ℝ) * Complex.I) with hω
  have hshift : ∀ x, F (x + 2 * π / 3) = ω * F x := by
    intro x
    have hc : Real.cos (3 * (x + 2 * π / 3)) = Real.cos (3 * x) := by
      rw [show 3 * (x + 2 * π / 3) = 3 * x + 2 * π by ring, Real.cos_add_two_pi]
    simp only [hF, hω, hc]
    rw [show -(d:ℂ) * ((x + 2 * π / 3 : ℝ) : ℂ) * Complex.I
        = -(d:ℂ) * (2 * π / 3 : ℝ) * Complex.I + -(d:ℂ) * (x : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_add]
    ring
  have hω1 : ω ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h
    have h2 : (2 * π * Complex.I : ℂ) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := by exact_mod_cast pi_pos.ne'
      simp [this, Complex.I_ne_zero]
    have h3 : ((-d : ℤ) : ℂ) = ((3 * k : ℤ) : ℂ) := by
      apply mul_left_cancel₀ h2
      push_cast at hk ⊢
      linear_combination 3 * hk
    have h4 : -d = 3 * k := by exact_mod_cast h3
    exact hd ⟨-k, by omega⟩
  have hI : (∫ x in (0:ℝ)..2 * π, F x) = ω * ∫ x in (0:ℝ)..2 * π, F x := by
    rw [← intervalIntegral.integral_const_mul]
    simp_rw [← hshift]
    rw [intervalIntegral.integral_comp_add_right, zero_add,
      add_comm (2 * π) (2 * π / 3), hper.intervalIntegral_add_eq (2 * π / 3) 0, zero_add]
  have h0 : (∫ x in (0:ℝ)..2 * π, F x) = 0 := by
    have : (ω - 1) * (∫ x in (0:ℝ)..2 * π, F x) = 0 := by rw [sub_mul, ← hI]; ring
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hω1)
  rw [h0, smul_zero]

end KsIndex.Trace
