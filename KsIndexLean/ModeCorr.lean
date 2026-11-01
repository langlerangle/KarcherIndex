module

/-
Boundary estimate for the finite-mode correction `groundR · Gpart`.

On the closed unit disk, `groundR_abs_le` proves
`|groundR k w| ≤ kap k * (2k−2) * (1 − ‖w‖)` for `k ≥ 2`.
The proof uses `groundR = kap k * (1−ρ)/(1+ρ)`, with
`ρ = ‖w‖^(2k−2)`, and the elementary power-difference estimate.

For `k ≥ 3` and `1 ≤ r ≤ k−1`, the nonzero lattice frequencies satisfy
`|ℓ(n)| ≥ 1`. Thus `norm_Gpart_le` bounds the finite sum by
`Σ_{|n|≤N} ‖t_n‖`, since each harmonic monomial has norm at most one on the disk.
Combining these facts gives `norm_correction_le`:

  `‖groundR · Gpart‖ ≤ kap k * (2k−2) * (1 − ‖w‖) * Σ_{|n|≤N} ‖t_n‖`.

This is a value estimate, not a gradient estimate. Its constant still contains
the finite coefficient mass. A bound uniform in `N` requires a separate bound
on those masses, for example from summability of the full coefficient sequence.
No Poisson-kernel or distance-to-support estimate is used here.
-/
public import KsIndexLean.ModePoisson

@[expose] public section


noncomputable section

open Real Set Complex
open KsIndex.Surface KsIndex.SingleDisk KsIndex.ModeKit KsIndex.ModeWitness
  KsIndex.ModePoisson KsIndex.Radial

namespace KsIndex.ModeCorr

variable {k r : ℕ}

/-! ### `groundR` vanishes linearly at the boundary -/

lemma groundR_abs_le (hk : 2 ≤ k) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    |groundR k w| ≤ kap k * (2 * (k : ℝ) - 2) * (1 - ‖w‖) := by
  set s := ‖w‖ with hs
  have hs0 : 0 ≤ s := norm_nonneg w
  have hnorm : w.re ^ 2 + w.im ^ 2 = s ^ 2 := by
    rw [hs, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hκ : 0 < kap k := kap_pos hk
  set ρ := (w.re ^ 2 + w.im ^ 2) ^ (k - 1) with hρdef
  have hρs : ρ = s ^ (2 * (k - 1)) := by rw [hρdef, hnorm, ← pow_mul]
  have hρ0 : 0 ≤ ρ := by rw [hρs]; positivity
  have hρ1 : ρ ≤ 1 := by rw [hρs]; exact pow_le_one₀ hs0 hw
  have hden : 0 < ρ + 1 := by linarith
  -- `1 − ρ ≤ (2(k−1))·(1 − s)` from `abs_pow_sub_pow_le`
  have hpow : 1 - ρ ≤ ((2 * (k - 1) : ℕ) : ℝ) * (1 - s) := by
    have h := abs_pow_sub_pow_le (a := (1:ℝ)) (b := s) (n := 2 * (k - 1))
    rw [one_pow, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s),
      abs_one, max_eq_left (by rwa [abs_of_nonneg hs0]) , one_pow, mul_one] at h
    rw [hρs]
    calc 1 - s ^ (2 * (k - 1)) = |1 - s ^ (2 * (k - 1))| :=
          (abs_of_nonneg (by
            have : s ^ (2 * (k - 1)) ≤ 1 := pow_le_one₀ hs0 hw
            linarith)).symm
      _ ≤ (1 - s) * ((2 * (k - 1) : ℕ) : ℝ) := h
      _ = ((2 * (k - 1) : ℕ) : ℝ) * (1 - s) := by ring
  have hcast : ((2 * (k - 1) : ℕ) : ℝ) = 2 * (k : ℝ) - 2 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ k)]; ring
  -- assemble
  have hnum : 0 ≤ kap k * (1 - ρ) := mul_nonneg hκ.le (by linarith)
  have hval : groundR k w = kap k * (1 - ρ) / (ρ + 1) := by
    rw [groundR, ← hρdef]; ring
  rw [hval, abs_of_nonneg (div_nonneg hnum hden.le)]
  calc kap k * (1 - ρ) / (ρ + 1) ≤ kap k * (1 - ρ) / 1 := by
        apply div_le_div_of_nonneg_left hnum (by norm_num) (by linarith)
    _ = kap k * (1 - ρ) := by rw [div_one]
    _ ≤ kap k * (((2 * (k - 1) : ℕ) : ℝ) * (1 - s)) :=
        mul_le_mul_of_nonneg_left hpow hκ.le
    _ = kap k * (2 * (k : ℝ) - 2) * (1 - s) := by rw [hcast]; ring

/-! ### `Gpart` is bounded by the coefficient `ℓ¹`-mass -/

lemma norm_coefOf_le (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) (t : ℤ → ℂ) (n : ℤ) :
    ‖coefOf k r t n‖ ≤ ‖t n‖ := by
  rw [coefOf, norm_div, Complex.norm_natCast]
  rcases eq_or_ne (t n) 0 with h0 | h0
  · rw [h0, norm_zero, zero_div]
  · rw [div_le_iff₀ (by
      have := one_le_natAbs_lz hk hr1 hrk n
      exact_mod_cast (by omega : 0 < (lz k r n).natAbs))]
    have h1 : (1 : ℝ) ≤ ((lz k r n).natAbs : ℝ) := by
      have := one_le_natAbs_lz hk hr1 hrk n
      exact_mod_cast this
    nlinarith [norm_nonneg (t n)]

lemma norm_Gpart_le (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) (N : ℕ) (t : ℤ → ℂ)
    {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖Gpart k r N t w‖ ≤ ∑ i : Fin (2 * N + 1), ‖t (slot N i)‖ := by
  unfold Gpart
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [norm_smul, norm_baseMode]
  calc ‖coefOf k r t (slot N i)‖ * ‖w‖ ^ (lz k r (slot N i)).natAbs
      ≤ ‖t (slot N i)‖ * 1 := by
        refine mul_le_mul (norm_coefOf_le hk hr1 hrk t _) ?_ (by positivity) (norm_nonneg _)
        exact pow_le_one₀ (norm_nonneg w) hw
    _ = ‖t (slot N i)‖ := mul_one _

/-! ### The correction bound -/

/-- The correction vanishes linearly at the boundary, with the finite coefficient mass
retained: `‖groundR·Gpart‖ ≤ κ(2k−2)(1 − ‖w‖)·Σ‖t_n‖`. -/
theorem norm_correction_le (hk : 3 ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) (N : ℕ) (t : ℤ → ℂ)
    {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖((groundR k w : ℝ) : ℂ) * Gpart k r N t w‖
      ≤ kap k * (2 * (k : ℝ) - 2) * (1 - ‖w‖)
        * ∑ i : Fin (2 * N + 1), ‖t (slot N i)‖ := by
  have hk2 : 2 ≤ k := by omega
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hg := groundR_abs_le hk2 hw
  have hG := norm_Gpart_le hk hr1 hrk N t hw
  have hGnn : (0:ℝ) ≤ ‖Gpart k r N t w‖ := norm_nonneg _
  have hgnn : (0:ℝ) ≤ kap k * (2 * (k : ℝ) - 2) * (1 - ‖w‖) := by
    have hκ := kap_pos hk2
    have : (0:ℝ) ≤ 1 - ‖w‖ := by linarith
    have h2 : (0:ℝ) ≤ 2 * (k : ℝ) - 2 := by
      have : (2:ℝ) ≤ k := by exact_mod_cast hk2
      linarith
    positivity
  calc |groundR k w| * ‖Gpart k r N t w‖
      ≤ (kap k * (2 * (k : ℝ) - 2) * (1 - ‖w‖)) * (∑ i : Fin (2 * N + 1), ‖t (slot N i)‖) :=
        mul_le_mul hg hG hGnn hgnn
    _ = kap k * (2 * (k : ℝ) - 2) * (1 - ‖w‖) * ∑ i : Fin (2 * N + 1), ‖t (slot N i)‖ := rfl

end KsIndex.ModeCorr
