module

public import KsIndexLean.AlphaFourModeGramAssembly

@[expose] public section


/-! Weighted Cauchy–Schwarz for complex sequences on the full integer lattice. -/
noncomputable section
namespace KsIndex.AlphaFourMode
open SIsometry

lemma weighted_complex_cauchy (F u : ℤ → ℂ) (D : ℤ → ℝ)
    (hD : ∀ n, 0 < D n)
    (hF : Summable (fun n => ‖F n‖^2 / D n))
    (hu : Summable (fun n => D n * ‖u n‖^2)) :
    ‖∑' n, F n * u n‖^2 ≤
      (∑' n, ‖F n‖^2 / D n) * (∑' n, D n * ‖u n‖^2) := by
  let p : ℤ → ℝ := fun n => ‖F n‖ * (Real.sqrt (D n))⁻¹
  let q : ℤ → ℝ := fun n => Real.sqrt (D n) * ‖u n‖
  have hsne : ∀ n, Real.sqrt (D n) ≠ 0 := fun n => Real.sqrt_ne_zero'.mpr (hD n)
  have hp2 : ∀ n, p n ^ 2 = ‖F n‖^2 / D n := by
    intro n
    simp only [p, mul_pow, inv_pow, Real.sq_sqrt (hD n).le, div_eq_mul_inv]
  have hq2 : ∀ n, q n ^ 2 = D n * ‖u n‖^2 := by
    intro n
    simp only [q, mul_pow, Real.sq_sqrt (hD n).le]
  have hpq : ∀ n, p n * q n = ‖F n * u n‖ := by
    intro n
    dsimp [p, q]
    rw [norm_mul]
    calc
      _ = ‖F n‖ * ‖u n‖ * ((Real.sqrt (D n))⁻¹ * Real.sqrt (D n)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (hsne n), mul_one]
  have hp : Summable (fun n => p n ^ 2) := hF.congr (fun n => (hp2 n).symm)
  have hq : Summable (fun n => q n ^ 2) := hu.congr (fun n => (hq2 n).symm)
  have hpqs := summable_mul_of_sq hp hq
  have hn : Summable (fun n => ‖F n * u n‖) := hpqs.congr hpq
  have hb : ‖∑' n, F n * u n‖ ≤ ∑' n, p n * q n :=
    (norm_tsum_le_tsum_norm hn).trans_eq (tsum_congr (fun n => (hpq n).symm))
  have hb2 := pow_le_pow_left₀ (norm_nonneg (∑' n, F n * u n)) hb 2
  have hc := tsum_mul_sq_le hp hq
  rw [tsum_congr hp2, tsum_congr hq2] at hc
  exact hb2.trans hc

end KsIndex.AlphaFourMode
