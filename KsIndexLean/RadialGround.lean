module

/-
Zero-mode energy and boundary vanishing of the radial ground state.

For `k ≥ 2`, the radial ground state `gRad k 0` has zero mode energy:

  `∫_0^1 lhs k 0 (gRad k 0) (gD k) = 0` (`qMode_zero_uRad`).

The proof applies the radial energy identity: the Wronskian and Picone remainder
of the ground state against itself vanish, and the boundary functional `Bd`
vanishes at both endpoints. The cancellation formula for `Bd` also holds at
zeros of the ground state, without dividing by a nonzero value there.

The file proves the linear boundary bound
`gRad k 0 r ≤ kap k * (2k−2) * (1−r)` on `[0,1]`, again for `k ≥ 2`.
This bound is used in cutoff-energy estimates for the class-zero mixed-boundary
construction. The cutoff construction and the negative Gram-form argument are
separate from the radial identities proved here.
-/
public import KsIndexLean.RadialMode

@[expose] public section


noncomputable section

open Set

namespace KsIndex.Radial

variable {k : ℕ}

/-- The Wronskian of the ground state against itself vanishes identically. -/
lemma Wg_zero_self (k : ℕ) (r : ℝ) : Wg k 0 (gRad k 0) (gD k) r = 0 := by
  simp only [Wg, Nat.cast_zero, zero_mul, zero_add]
  ring

/-- The Picone remainder of the ground state against itself vanishes identically. -/
lemma Rm_zero_self (k : ℕ) (r : ℝ) : Rm k 0 (gRad k 0) (gD k) r = 0 := by
  rw [Rm, Wg_zero_self]
  simp

lemma Bd_zero_self_zero (k : ℕ) : Bd k 0 (gRad k 0) 0 = 0 := by
  simp [Bd]

lemma Bd_zero_self_one (hk : 2 ≤ k) : Bd k 0 (gRad k 0) 1 = 0 := by
  rw [Bd, gRad_zero_one hk]
  simp

/-- `Bd` of the ground state is the product `r g' g` (the division cancels; where `g = 0` both
sides vanish). -/
lemma Bd_zero_self_eq (k : ℕ) (r : ℝ) :
    Bd k 0 (gRad k 0) r = r * gD k r * gRad k 0 r := by
  rw [Bd]
  rcases eq_or_ne (gRad k 0 r) 0 with h0 | h0
  · rw [h0]; simp
  · simp only [Nat.cast_zero, zero_mul, zero_add]
    field_simp

/-- **The ℓ = 0 ground state has zero mode energy**:
`∫_0^1 (r g'² − r V g²) dr = 0` for `g = gRad k 0`. -/
theorem qMode_zero_uRad (hk : 2 ≤ k) :
    ∫ r in (0 : ℝ)..1, lhs k 0 (gRad k 0) (gD k) r = 0 := by
  have hf : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivAt (gRad k 0) (gD k r) r :=
    fun r _ => gRad_hasDerivAt hk 0 r
  have hf' : ContinuousOn (gD k) (Icc 0 1) :=
    fun r _ => (gD_hasDerivAt hk r).continuousAt.continuousWithinAt
  have hg : ∀ r ∈ Ioo (0 : ℝ) 1, gRad k 0 r ≠ 0 :=
    fun r hr => (gRad_zero_pos hk hr.1.le hr.2).ne'
  have hBc : ContinuousOn (Bd k 0 (gRad k 0)) (Icc 0 1) := by
    refine ContinuousOn.congr ?_ (fun r _ => Bd_zero_self_eq k r)
    exact (continuousOn_id.mul
        (fun r _ => (gD_hasDerivAt hk r).continuousAt.continuousWithinAt)).mul
      (fun r hr => (hf r hr).continuousAt.continuousWithinAt)
  obtain ⟨-, h⟩ := qMode_ftc hk 0 hf (lhs_zero_continuousOn hf hf') hg hBc
  rw [h, Bd_zero_self_zero, Bd_zero_self_one hk]
  have h0 : ∫ r in (0 : ℝ)..1, Rm k 0 (gRad k 0) (gD k) r = 0 := by
    simp only [Rm_zero_self]
    simp
  rw [h0]
  ring

/-- `1 − r^n ≤ n(1 − r)` on `[0, 1]`. -/
lemma one_sub_pow_le (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    1 - r ^ n ≤ n * (1 - r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : 0 ≤ 1 - r ^ n := by
      have := pow_le_one₀ hr0 hr1 (n := n)
      linarith
    have key : r * (1 - r ^ n) ≤ 1 - r ^ n := mul_le_of_le_one_left hpow hr1
    have hexp : 1 - r ^ (n + 1) = (1 - r) + r * (1 - r ^ n) := by rw [pow_succ]; ring
    rw [hexp]
    push_cast
    linarith [ih, key]

/-- **Linear vanishing of the ground state at the boundary**:
`gRad k 0 r ≤ κ_k (2k−2)(1−r)` on `[0,1]` (the bound that makes cutting the ground state off
near the boundary collar energy-cheap). -/
lemma gRad_zero_le_lin (hk : 2 ≤ k) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    gRad k 0 r ≤ kap k * ((2 * k - 2 : ℕ) : ℝ) * (1 - r) := by
  have hs0 : 0 ≤ r ^ (2 * k - 2) := pow_even_nonneg k r
  have hκ : 0 < kap k := kap_pos hk
  have hpow := one_sub_pow_le (2 * k - 2) hr0 hr1
  rw [gRad, div_le_iff₀ (denom_pos k r)]
  have h1 : kap k * (1 - r ^ (2 * k - 2))
      ≤ kap k * (((2 * k - 2 : ℕ) : ℝ) * (1 - r)) :=
    mul_le_mul_of_nonneg_left hpow hκ.le
  have h2 : 0 ≤ kap k * ((2 * k - 2 : ℕ) : ℝ) * (1 - r) * r ^ (2 * k - 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg hκ.le (Nat.cast_nonneg _)) (by linarith)) hs0
  push_cast at h1 h2 ⊢
  nlinarith [h1, h2]

end KsIndex.Radial
