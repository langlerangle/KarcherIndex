module

public import KsIndexLean.PowerArcStieltjesSplit
public import KsIndexLean.PowerArcConvolution

@[expose] public section


/-! Assembly of finite prefix and endpoint certificates into a full Stieltjes enclosure. -/

namespace KsIndex.PowerArc

theorem powerArcStieltjes_enclosure (β r B z M p q ε δ : ℝ) (N : ℕ)
    (hβ : 0 < β) (hr : β ≤ r) (hBdef : B = (r + β + 2) / 2)
    (hz : 0 < z) (hM : 1 ≤ M) (hend : B + N + 2 ≤ M * (z + N))
    (hp : |normalizedStieltjesPrefix β r z N - p| ≤ ε)
    (hq : |normalizedCoefficient β r N - q| ≤ δ) :
    let L := 1 / (β + 1) + (B - z) / ((β + 2) * (B + N))
    let C := |(B - z) * (B + 1 - z)| * M /
      ((β + 3) * (B + N) * (B + N + 1))
    |powerArcStieltjes β r z - g β r * (p + (-1 : ℝ) ^ N * q * L)| ≤
      |g β r| * (ε + |L| * δ + C * (|q| + δ)) := by
  dsimp only
  let L := 1 / (β + 1) + (B - z) / ((β + 2) * (B + N))
  let C := |(B - z) * (B + 1 - z)| * M /
    ((β + 3) * (B + N) * (B + N + 1))
  let P := normalizedStieltjesPrefix β r z N
  let Q := normalizedCoefficient β r N
  change |powerArcStieltjes β r z - g β r * (p + (-1 : ℝ) ^ N * q * L)| ≤
    |g β r| * (ε + |L| * δ + C * (|q| + δ))
  have hB : 0 < B := by rw [hBdef]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have htail : |powerArcStieltjes β r z - g β r * (P + (-1 : ℝ) ^ N * Q * L)| ≤
      |g β r| * C * |Q| := by
    have hh := powerArcStieltjes_tail_bound β r B z M N hβ hr hBdef hz hM hend
    rw [g_eq_normalizedCoefficient hβ (by linarith : 0 ≤ r)] at hh
    convert hh using 1
    · dsimp [P, Q, L]
      congr 1
      ring
    · dsimp [C, Q]
      simp only [abs_mul]
      ring
  have hQ : |Q| ≤ |q| + δ := by
    have hh : |Q| ≤ |Q - q| + |q| := by
      simpa only [sub_add_cancel] using abs_add_le (Q - q) q
    dsimp [Q] at hh ⊢
    linarith
  have hcenter : |g β r * (P + (-1 : ℝ) ^ N * Q * L) -
      g β r * (p + (-1 : ℝ) ^ N * q * L)| ≤ |g β r| * (ε + |L| * δ) := by
    have hid : g β r * (P + (-1 : ℝ) ^ N * Q * L) -
        g β r * (p + (-1 : ℝ) ^ N * q * L) =
        g β r * ((P - p) + (-1 : ℝ) ^ N * (Q - q) * L) := by ring
    rw [hid, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc
      _ ≤ |P - p| + |(-1 : ℝ) ^ N * (Q - q) * L| := abs_add_le _ _
      _ = |P - p| + |L| * |Q - q| := by
        rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        ring
      _ ≤ ε + |L| * δ := add_le_add hp (mul_le_mul_of_nonneg_left hq (abs_nonneg _))
  calc
    _ ≤ |powerArcStieltjes β r z - g β r * (P + (-1 : ℝ) ^ N * Q * L)| +
        |g β r * (P + (-1 : ℝ) ^ N * Q * L) - g β r * (p + (-1 : ℝ) ^ N * q * L)| :=
      abs_sub_le _ _ _
    _ ≤ |g β r| * C * (|q| + δ) + |g β r| * (ε + |L| * δ) :=
      add_le_add (htail.trans (mul_le_mul_of_nonneg_left hQ (mul_nonneg (abs_nonneg _) hC))) hcenter
    _ = _ := by ring

/-- The same enclosure in the normalization used by the concrete trial. -/
theorem normalized_powerArcStieltjes_enclosure (β r B z M p q ε δ : ℝ) (N : ℕ)
    (hβ : 0 < β) (hr : β ≤ r) (hBdef : B = (r + β + 2) / 2)
    (hz : 0 < z) (hM : 1 ≤ M) (hend : B + N + 2 ≤ M * (z + N))
    (hp : |normalizedStieltjesPrefix β r z N - p| ≤ ε)
    (hq : |normalizedCoefficient β r N - q| ≤ δ) :
    let L := 1 / (β + 1) + (B - z) / ((β + 2) * (B + N))
    let C := |(B - z) * (B + 1 - z)| * M /
      ((β + 3) * (B + N) * (B + N + 1))
    |powerArcStieltjes β r z / g β 0 -
      (g β r / g β 0) * (p + (-1 : ℝ) ^ N * q * L)| ≤
      |g β r / g β 0| * (ε + |L| * δ + C * (|q| + δ)) := by
  have hg0 : 0 < g β 0 := g_pos_of_mem_unit hβ (by norm_num) (by norm_num)
  have hh := div_le_div_of_nonneg_right
    (powerArcStieltjes_enclosure β r B z M p q ε δ N hβ hr hBdef hz hM hend hp hq) hg0.le
  dsimp only at hh ⊢
  convert! hh using 1
  · rw [div_mul_eq_mul_div, ← sub_div, abs_div, abs_of_pos hg0]
  · rw [abs_div, abs_of_pos hg0]
    ring

end KsIndex.PowerArc
