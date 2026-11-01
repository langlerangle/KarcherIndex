module

public import KsIndexLean.AlphaStieltjesCompensated
public import KsIndexLean.PowerArcNormalizedEnergy

@[expose] public section


/-! Infinite weighted-energy bounds for the compensated power-arc groups. -/

namespace KsIndex.PowerArc

/-- The actual compensated group has a summable weighted square tail with an
explicit bound in terms of its initial value and the Stieltjes correction coefficient. -/
theorem compensatedPowerArcGroup_energy (β r κ w : ℝ) (N : ℕ)
    (hβ : β = 4323618 / 10000000 ∨ β = 5676382 / 10000000)
    (hr : r = 14 ∨ r = 15) (hN : 1024 ≤ N) :
    let C := |compensatedPowerArcGroup β r κ w N| +
      11 * |stieltjesCorrectionD β r κ| / ((N : ℝ) + 9 / 2) ^ 3
    let t := 2 * (N : ℝ) + 9 - r
    Summable (fun n : ℕ => (6 * ((N + n : ℕ) : ℝ) + 1) *
      compensatedPowerArcGroup β r κ w (N + n) ^ 2) ∧
      (∑' n : ℕ, (6 * ((N + n : ℕ) : ℝ) + 1) *
        compensatedPowerArcGroup β r κ w (N + n) ^ 2) ≤
        (C ^ 2 * ((6 * N + 1) / t)) * ((t + β) ^ 2 / (4 * β)) := by
  dsimp only
  let t : ℝ := 2 * N + 9 - r
  let C := |compensatedPowerArcGroup β r κ w N| +
    11 * |stieltjesCorrectionD β r κ| / ((N : ℝ) + 9 / 2) ^ 3
  have hn : (1024 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : 0 < t := by dsimp [t]; rcases hr with rfl | rfl <;> linarith
  have hb : 0 < β := by rcases hβ with rfl | rfl <;> norm_num
  have ha : (0 : ℝ) ≤ 6 * N + 1 := by positivity
  have haM : (6 * (N : ℝ) + 1) ≤ ((6 * N + 1) / t) * t := by
    rw [div_mul_cancel₀ _ (ne_of_gt ht)]
  have hbM : (6 : ℝ) ≤ 2 * ((6 * N + 1) / t) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ ht).2
    dsimp [t]
    rcases hr with rfl | rfl <;> linarith
  have hh := normalized_envelope_energy β t C ((6 * N + 1) / t) (6 * N + 1) 6
    (fun n => compensatedPowerArcGroup β r κ w (N + n)) hb ht.le
    (div_nonneg ha ht.le) ha (by norm_num) haM hbM
    (fun n => compensatedPowerArcGroup_normalized_bound β r κ w N hβ hr hN n)
  have hw (n : ℕ) : (6 * (N : ℝ) + 1) + 6 * n = 6 * ((N + n : ℕ) : ℝ) + 1 := by
    push_cast; ring
  simp only [hw] at hh
  exact hh

end KsIndex.PowerArc
