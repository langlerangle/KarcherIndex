module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section


/-! Exact period arithmetic for a real number in the certified decimal interval.
This module has no dependency on the numerical proof stacks. -/
namespace KsIndex.DecimalPeriodArithmetic

theorem nonresonant {a : ℝ} (hl : (163 : ℝ) / 377 < a)
    (hu : a < (831 : ℝ) / 1922) {m : ℕ} (hm : 0 < m) (hbound : m ≤ 2298) :
    ¬ ∃ z : ℤ, (m : ℝ) * a = (z : ℝ) := by
  rintro ⟨z, hz⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hL := mul_lt_mul_of_pos_left hl hmR
  have hU := mul_lt_mul_of_pos_left hu hmR
  rw [hz] at hL hU
  have hA : (0 : ℝ) < 377 * (z : ℝ) - 163 * (m : ℝ) := by linarith
  have hB : (0 : ℝ) < 831 * (m : ℝ) - 1922 * (z : ℝ) := by linarith
  have hAi : (0 : ℤ) < 377 * z - 163 * (m : ℤ) := by exact_mod_cast hA
  have hBi : (0 : ℤ) < 831 * (m : ℤ) - 1922 * z := by exact_mod_cast hB
  have hmi : (m : ℤ) ≤ 2298 := by exact_mod_cast hbound
  omega

theorem decimal_nonresonant {a : ℝ} (hl : (4323617 : ℝ) / 10000000 < a)
    (hu : a < (4323619 : ℝ) / 10000000) {m : ℕ} (hm : 0 < m)
    (hbound : m ≤ 2298) : ¬ ∃ z : ℤ, (m : ℝ) * a = (z : ℝ) := by
  apply nonresonant (lt_trans (by norm_num) hl) (lt_trans hu (by norm_num)) hm hbound

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem upper_certificate : ∀ m : Fin 2299,
    4323619 * m.val < (4323617 * m.val / 10000000 + 1) * 10000000 := by
  decide

theorem decimal_interval {a : ℝ} (hl : (4323617 : ℝ) / 10000000 < a)
    (hu : a < (4323619 : ℝ) / 10000000) {m : ℕ} (hm : 0 < m)
    (hbound : m ≤ 2298) :
    ((4323617 * m / 10000000 : ℕ) : ℝ) < (m : ℝ) * a ∧
    (m : ℝ) * a < ((4323617 * m / 10000000 : ℕ) : ℝ) + 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hL := mul_lt_mul_of_pos_left hl hmR
  have hU := mul_lt_mul_of_pos_left hu hmR
  have hlow := Nat.div_mul_le_self (4323617 * m) 10000000
  have hupp := upper_certificate ⟨m, by omega⟩
  have hlowR : ((4323617 * m / 10000000 : ℕ) : ℝ) * 10000000 ≤ 4323617 * (m : ℝ) := by
    exact_mod_cast hlow
  have huppR : 4323619 * (m : ℝ) < (((4323617 * m / 10000000 : ℕ) : ℝ) + 1) * 10000000 := by
    exact_mod_cast hupp
  constructor <;> linarith

theorem decimal_floor {a : ℝ} (hl : (4323617 : ℝ) / 10000000 < a)
    (hu : a < (4323619 : ℝ) / 10000000) {m : ℕ} (hm : 0 < m)
    (hbound : m ≤ 2298) : ⌊(m : ℝ) * a⌋₊ = 4323617 * m / 10000000 := by
  have h := decimal_interval hl hu hm hbound
  rw [Nat.floor_eq_iff (by positivity : (0 : ℝ) ≤ (m : ℝ) * a)]
  exact ⟨h.1.le, h.2⟩

end KsIndex.DecimalPeriodArithmetic
