module

public import KsIndexLean.PowerArcRounding
public import KsIndexLean.CertifiedApproximation

@[expose] public section


/-! Integer accumulation with explicit errors for signed rational linear sums. -/
namespace KsIndex.CertifiedApproximation

/-- The two extra integer units cover rounding of both center and radius. -/
theorem integer_weighted_linear_error {x : ℝ} (p a e : ℤ) {q S : ℤ}
    (hq : 0 < q) (hS : 0 < S)
    (hx : |x - (a:ℝ)/S| ≤ (e:ℝ)/S) :
    |(p:ℝ)/q*x - ((p*a/q:ℤ):ℝ)/S| ≤ ((|p| * e/q+2:ℤ):ℝ)/S := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hSR : (0:ℝ) < S := by exact_mod_cast hS
  have hw := mul_le_mul_of_nonneg_left hx (abs_nonneg ((p:ℝ)/q))
  have hc := PowerArc.int_quotient_rounding_error (p*a) hq
  have hr := (abs_le.mp (PowerArc.int_quotient_rounding_error (|p| * e) hq)).2
  have hid : (p:ℝ)/q*((a:ℝ)/S) = ((p*a:ℤ):ℝ)/q/S := by push_cast; ring
  have hrad : |(p:ℝ)/q| * ((e:ℝ)/S) = ((|p| * e:ℤ):ℝ)/q/S := by
    rw [abs_div, abs_of_pos hqR]
    push_cast
    ring
  rw [← abs_mul, mul_sub, hid, hrad] at hw
  have hround : |((p*a:ℤ):ℝ)/q/S - ((p*a/q:ℤ):ℝ)/S| ≤ 1/(S:ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hSR]
    exact div_le_div_of_nonneg_right hc hSR.le
  have ht := (abs_sub_le ((p:ℝ)/q*x) (((p*a:ℤ):ℝ)/q/S)
    (((p*a/q:ℤ):ℝ)/S)).trans (add_le_add hw hround)
  have he := div_le_div_of_nonneg_right hr hSR.le
  push_cast at he ⊢
  rw [sub_div] at he
  push_cast at ht
  rw [add_div]
  linarith [show (2:ℝ)/S = 1/S+1/S by ring]

/-- Finite signed linear combinations inherit the sum of the integer radii. -/
theorem finite_integer_linear_error {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (p q a e : ι → ℤ) {S : ℤ} (hS : 0 < S)
    (hq : ∀ i ∈ s, 0 < q i)
    (hx : ∀ i ∈ s, |x i - (a i:ℝ)/S| ≤ (e i:ℝ)/S) :
    |(∑ i ∈ s, (p i:ℝ)/q i*x i) - ((∑ i ∈ s, p i*a i/q i:ℤ):ℝ)/S| ≤
      ((∑ i ∈ s, (|p i| * e i/q i+2):ℤ):ℝ)/S := by
  have hh := finite_linear_error s (fun _ => (1:ℝ))
    (fun i => (p i:ℝ)/q i*x i) (fun i => ((p i*a i/q i:ℤ):ℝ)/S)
    (fun i => ((|p i| * e i/q i+2:ℤ):ℝ)/S)
    (fun i hi => integer_weighted_linear_error (p i) (a i) (e i) (hq i hi) hS (hx i hi))
  simpa only [one_mul, abs_one, Int.cast_sum, Finset.sum_div] using hh

end KsIndex.CertifiedApproximation
