module

public import KsIndexLean.PowerArcNormalized
public import KsIndexLean.PowerArcConvolution

@[expose] public section


/-! Shared seed dependence of normalized power-arc coefficients. -/

namespace KsIndex.PowerArc

/-- Even coefficients are independent of the odd seed; odd coefficients share
one common seed factor. Keeping that factor outside sums preserves cancellation. -/
theorem normalized_g_parity {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    g β (n : ℝ) / g β 0 =
      if n % 2 = 0 then normalizedCoefficient β 0 (n / 2)
      else (g β 1 / g β 0) * normalizedCoefficient β 1 (n / 2) := by
  have hg : g β 0 ≠ 0 := ne_of_gt (g_pos_of_mem_unit hβ (by norm_num) (by norm_num))
  by_cases hn : n % 2 = 0
  · rw [ite_eq_left hn]
    have he : (n : ℝ) = 0 + 2 * (n / 2 : ℕ) := by
      have hh : n = 2 * (n / 2) := by omega
      simpa only [zero_add] using (show (n : ℝ) = 2 * (n / 2 : ℕ) by exact_mod_cast hh)
    rw [he, g_eq_normalizedCoefficient hβ (by norm_num)]
    field_simp
  · rw [ite_eq_right hn]
    have he : (n : ℝ) = 1 + 2 * (n / 2 : ℕ) := by
      have hh : n = 1 + 2 * (n / 2) := by omega
      exact_mod_cast hh
    rw [he, g_eq_normalizedCoefficient hβ (by norm_num)]
    ring

/-- A finite linear combination uses the odd seed only once, after all signed
coefficients in its parity class have been combined. -/
theorem sum_normalized_g_seed_linear {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (n : ι → ℕ) {β : ℝ} (hβ : 0 < β) :
    (∑ i ∈ s, c i * (g β (n i : ℝ) / g β 0)) =
      (∑ i ∈ s, if n i % 2 = 0 then c i * normalizedCoefficient β 0 (n i / 2) else 0) +
      (g β 1 / g β 0) *
        ∑ i ∈ s, if n i % 2 = 0 then 0 else c i * normalizedCoefficient β 1 (n i / 2) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [normalized_g_parity hβ]
  by_cases hn : n i % 2 = 0
  · simp only [hn, ite_true, mul_zero, add_zero]
  · simp only [hn, ite_false, zero_add]
    ring

end KsIndex.PowerArc
