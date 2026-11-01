module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

@[expose] public section


/-! Arithmetic of a floor staircase and its successive increments. -/
namespace KsIndex.StaircaseIncrements

/-- For slopes between zero and one, consecutive floors differ by zero or one. -/
theorem floor_step {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    ⌊((n + 1 : ℕ) : ℝ) * a⌋ = ⌊(n : ℝ) * a⌋ ∨
    ⌊((n + 1 : ℕ) : ℝ) * a⌋ = ⌊(n : ℝ) * a⌋ + 1 := by
  have hl := Int.floor_mono (show (n : ℝ)*a ≤ ((n+1 : ℕ) : ℝ)*a by push_cast; nlinarith)
  have hu := Int.floor_mono (show ((n+1 : ℕ) : ℝ)*a ≤ (n : ℝ)*a+1 by push_cast; nlinarith)
  rw [Int.floor_add_one] at hu
  omega

/-- The integer staircase has successive increments two or six, including at resonance. -/
theorem index_step {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    (6 * (n+1 : ℤ) - 4 * ⌊((n+1 : ℕ) : ℝ)*a⌋ - 3) =
      (6 * (n : ℤ) - 4 * ⌊(n : ℝ)*a⌋ - 3) + 2 ∨
    (6 * (n+1 : ℤ) - 4 * ⌊((n+1 : ℕ) : ℝ)*a⌋ - 3) =
      (6 * (n : ℤ) - 4 * ⌊(n : ℝ)*a⌋ - 3) + 6 := by
  rcases floor_step ha ha1 n with h | h <;> omega

/-- Eventually periodic differences give affine values along a period subsequence. -/
theorem periodic_blocks (F : ℕ → ℤ) (N p : ℕ)
    (h : ∀ n, N ≤ n → F (n + p + 1) - F (n + p) = F (n + 1) - F n) :
    ∀ j, F (N+j*p) = F N + (j : ℤ)*(F (N+p)-F N) := by
  have hd : ∀ t, F (N+t+p)-F (N+t) = F (N+p)-F N := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hh := h (N+t) (by omega)
      have he : N+(t+1)+p = N+t+p+1 := by omega
      have he' : N+(t+1) = N+t+1 := by omega
      rw [he, he']
      omega
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hh := hd (j*p)
    have he : N+(j+1)*p = N+j*p+p := by ring
    rw [he]
    push_cast
    nlinarith

/-- Eventual periodicity of floor differences forces the slope to be rational. -/
theorem rational_of_eventually_periodic_floor {a : ℝ} {N p : ℕ} (hp : 0 < p)
    (h : ∀ n, N ≤ n →
      ⌊((n + p + 1 : ℕ) : ℝ) * a⌋ - ⌊((n + p : ℕ) : ℝ) * a⌋ =
      ⌊((n + 1 : ℕ) : ℝ) * a⌋ - ⌊(n : ℝ) * a⌋) :
    ∃ q : ℚ, a = q := by
  let A : ℤ := ⌊((N+p : ℕ) : ℝ)*a⌋ - ⌊(N : ℝ)*a⌋
  have hb := periodic_blocks (fun n => ⌊(n : ℝ)*a⌋) N p h
  have he : ∀ j : ℕ, -1 < (j : ℝ)*((p : ℝ)*a-(A : ℝ)) ∧
      (j : ℝ)*((p : ℝ)*a-(A : ℝ)) < 1 := by
    intro j
    have hbj : (⌊((N+j*p : ℕ) : ℝ)*a⌋ : ℝ) =
        (⌊(N : ℝ)*a⌋ : ℝ)+(j : ℝ)*(A : ℝ) := by
      exact_mod_cast hb j
    have hlo := Int.floor_le (((N+j*p : ℕ) : ℝ)*a)
    have hhi := Int.lt_floor_add_one (((N+j*p : ℕ) : ℝ)*a)
    have hNlo := Int.floor_le ((N : ℝ)*a)
    have hNhi := Int.lt_floor_add_one ((N : ℝ)*a)
    push_cast at hlo hhi hbj
    constructor <;> nlinarith
  have hz : (p : ℝ)*a-(A : ℝ) = 0 := by
    rcases lt_trichotomy ((p : ℝ)*a-(A : ℝ)) 0 with hn | hz | hp'
    · obtain ⟨j, hj⟩ := exists_nat_gt (1 / (-((p : ℝ)*a-(A : ℝ))))
      have hm := (div_lt_iff₀ (neg_pos.mpr hn)).mp hj
      have hh := (he j).1
      nlinarith
    · exact hz
    · obtain ⟨j, hj⟩ := exists_nat_gt (1 / ((p : ℝ)*a-(A : ℝ)))
      have hm := (div_lt_iff₀ hp').mp hj
      have hh := (he j).2
      nlinarith
  refine ⟨(A : ℚ)/(p : ℚ), ?_⟩
  push_cast
  apply (eq_div_iff (by exact_mod_cast (Nat.ne_of_gt hp) : (p : ℝ) ≠ 0)).mpr
  nlinarith

/-- For `I n = 6*n - 4*floor(n*a) - 3`, eventual periodicity of successive
increments forces the slope `a` to be rational. -/
theorem rational_of_eventually_periodic_index {a : ℝ} (I : ℕ → ℤ)
    (hI : ∀ n, 1 ≤ n → I n = 6 * (n : ℤ) - 4 * ⌊(n : ℝ) * a⌋ - 3)
    {N p : ℕ} (hp : 0 < p)
    (hperiod : ∀ n, N ≤ n → I (n + p + 1) - I (n + p) = I (n + 1) - I n) :
    ∃ q : ℚ, a = q := by
  apply rational_of_eventually_periodic_floor (N := max N 1) hp
  intro n hn
  have h := hperiod n (le_trans (le_max_left _ _) hn)
  rw [hI (n+p+1) (by omega), hI (n+p) (by omega),
    hI (n+1) (by omega), hI n (by omega)] at h
  push_cast at h ⊢
  omega

#print axioms rational_of_eventually_periodic_index
#print axioms rational_of_eventually_periodic_floor
#print axioms floor_step
#print axioms index_step
#print axioms periodic_blocks
end KsIndex.StaircaseIncrements
