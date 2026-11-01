module

public import KsIndexLean.PowerArcRounding
public import KsIndexLean.CertifiedApproximation

@[expose] public section


/-! Certified approximation errors for individual power-arc samples. -/

namespace KsIndex.PowerArc

/-- A rounded recurrence and a seed enclosure together control every sample. -/
theorem rounded_sample_error {B D r S : ℤ} (hB : 0 < B) (hD : 0 < D)
    (hr : 0 ≤ r) (hS : 0 < S) {z δ : ℝ}
    (hseed : |g ((B : ℝ) / D) r / g ((B : ℝ) / D) 0 - z| ≤ δ) (n : ℕ) :
    |g ((B : ℝ) / D) (r + 2 * n) / g ((B : ℝ) / D) 0 -
      z * ((roundedCoefficient B D r S n : ℝ) / S)| ≤
      |(roundedCoefficient B D r S n : ℝ) / S| * δ +
      |z| * (n * (1 / (S : ℝ))) + (n * (1 / (S : ℝ))) * δ := by
  have hh := CertifiedApproximation.product_error
    (by positivity : (0 : ℝ) ≤ n * (1 / (S : ℝ)))
    (roundedCoefficient_error hB hD hr hS n) hseed
  have hβ : (0 : ℝ) < (B : ℝ) / D := by positivity
  have heq : g ((B : ℝ) / D) (r + 2 * n) / g ((B : ℝ) / D) 0 =
      normalizedCoefficient ((B : ℝ) / D) r n *
        (g ((B : ℝ) / D) r / g ((B : ℝ) / D) 0) := by
    rw [g_eq_normalizedCoefficient hβ (by exact_mod_cast hr)]
    ring
  rw [heq]
  simpa only [mul_comm z] using hh

end KsIndex.PowerArc
