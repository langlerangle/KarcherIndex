module

public import KsIndexLean.PowerArcRounding
public import KsIndexLean.CertifiedApproximation

@[expose] public section


/-! Integer accumulators with rigorous error bounds for quadratic energies. -/

namespace KsIndex.CertifiedApproximation

/-- Integer division is rounded down, with two units covering the rounding of
both the central value and its error radius. The weight numerator may be negative. -/
theorem integer_weighted_square_error {x : ℝ} (p a e : ℤ) {q T : ℤ}
    (hq : 0 < q) (hT : 0 < T) (he : 0 ≤ e)
    (hx : |x - (a : ℝ) / T| ≤ (e : ℝ) / T) :
    |(p : ℝ) / q * x ^ 2 - ((p * a ^ 2 / q : ℤ) : ℝ) / (T : ℝ) ^ 2| ≤
      ((|p| * e * (2 * |a| + e) / q + 2 : ℤ) : ℝ) / (T : ℝ) ^ 2 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have he' : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hs := square_error (div_nonneg he' hT'.le) hx
  have hw := mul_le_mul_of_nonneg_left hs (abs_nonneg ((p : ℝ) / q))
  have hc := PowerArc.int_quotient_rounding_error (p * a ^ 2) hq
  have hr := PowerArc.int_quotient_rounding_error (|p| * e * (2 * |a| + e)) hq
  have hr' := (abs_le.mp hr).2
  have hcentral : (p : ℝ) / q * ((a : ℝ) / T) ^ 2 =
      ((p * a ^ 2 : ℤ) : ℝ) / q / (T : ℝ) ^ 2 := by
    push_cast
    ring
  have hrad : |(p : ℝ) / q| * ((e : ℝ) / T * (2 * |(a : ℝ) / T| + (e : ℝ) / T)) =
      ((|p| * e * (2 * |a| + e) : ℤ) : ℝ) / q / (T : ℝ) ^ 2 := by
    rw [abs_div, abs_div, abs_of_pos hq', abs_of_pos hT']
    push_cast
    ring
  rw [← abs_mul, mul_sub, hcentral, hrad] at hw
  have hround : |((p * a ^ 2 : ℤ) : ℝ) / q / (T : ℝ) ^ 2 -
      ((p * a ^ 2 / q : ℤ) : ℝ) / (T : ℝ) ^ 2| ≤ 1 / (T : ℝ) ^ 2 := by
    rw [← sub_div, abs_div, abs_of_pos (sq_pos_of_pos hT')]
    exact div_le_div_of_nonneg_right hc (sq_nonneg _)
  have htriangle := abs_add_le
    ((p : ℝ) / q * x ^ 2 - ((p * a ^ 2 : ℤ) : ℝ) / q / (T : ℝ) ^ 2)
    (((p * a ^ 2 : ℤ) : ℝ) / q / (T : ℝ) ^ 2 -
      ((p * a ^ 2 / q : ℤ) : ℝ) / (T : ℝ) ^ 2)
  have hbound := div_le_div_of_nonneg_right hr' (sq_nonneg (T : ℝ))
  push_cast
  calc
    _ ≤ _ := by simpa only [sub_add_sub_cancel] using htriangle
    _ ≤ _ := add_le_add hw hround
    _ ≤ _ := by
      rw [sub_div] at hbound
      rw [add_div]
      linarith [show (2 : ℝ) / (T : ℝ) ^ 2 = 1 / (T : ℝ) ^ 2 + 1 / (T : ℝ) ^ 2 by ring]

theorem finite_integer_energy_error {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (p q a e : ι → ℤ) {T : ℤ} (hT : 0 < T)
    (hq : ∀ i ∈ s, 0 < q i) (he : ∀ i ∈ s, 0 ≤ e i)
    (hx : ∀ i ∈ s, |x i - (a i : ℝ) / T| ≤ (e i : ℝ) / T) :
    |(∑ i ∈ s, (p i : ℝ) / q i * x i ^ 2) -
      ((∑ i ∈ s, p i * a i ^ 2 / q i : ℤ) : ℝ) / (T : ℝ) ^ 2| ≤
      ((∑ i ∈ s, (|p i| * e i * (2 * |a i| + e i) / q i + 2) : ℤ) : ℝ) /
        (T : ℝ) ^ 2 := by
  have hh := finite_linear_error s (fun _ => (1 : ℝ))
    (fun i => (p i : ℝ) / q i * x i ^ 2)
    (fun i => ((p i * a i ^ 2 / q i : ℤ) : ℝ) / (T : ℝ) ^ 2)
    (fun i => ((|p i| * e i * (2 * |a i| + e i) / q i + 2 : ℤ) : ℝ) / (T : ℝ) ^ 2)
    (fun i hi => integer_weighted_square_error (p i) (a i) (e i)
      (hq i hi) hT (he i hi) (hx i hi))
  simpa only [one_mul, abs_one, Int.cast_sum, Int.cast_add, Int.cast_ofNat,
    Finset.sum_div] using hh

end KsIndex.CertifiedApproximation
