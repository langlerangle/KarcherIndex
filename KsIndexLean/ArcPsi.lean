module

/-
# The coefficient test for the paper's `Q-lower` estimate

The paper uses a piecewise multiple of `1 - exp(-iθ)`: its multiplier is
one on the half-arc and `(2-π)/(2+π)` off it. This file works with the
corresponding real coefficient formula `psiHat`, expressed using the
square-wave coefficients `sgnHat`.

For `u ∈ ArcDom`, the two support identities at frequencies `0` and `-1`
give `∑' ℓ, psiHat ℓ * u ℓ = u 0 - u (-1)`. The coefficients vanish at
those two frequencies. Away from them, their squares are
`4/(2+π)^2 * 1/(2j+1)^2` on the pairs `{2j, 2j+1}`.

The positive-tail estimate and summability of `Sconst` hold for
`0 < a < 1` and `|b| ≤ 1`. The final weighted Cauchy–Schwarz theorem
`head_diff_sq_le` assumes `|b| < 1` and `u ∈ ArcDom`, and bounds
`‖u 0 - u (-1)‖²` by `Sconst a b` times the tail energy.
-/
public import KsIndexLean.ArcForm

@[expose] public section


noncomputable section

namespace KsIndex.ArcPsi

open KsIndex.ArcSpace KsIndex.ArcForm KsIndex.CircleQ KsIndex.SIsometry Real

/-! ### `Ψ̂` -/

/-- The Fourier coefficients of `Ψ`. -/
def psiHat (ℓ : ℤ) : ℝ :=
  2 / (2 + π) * ((if ℓ = 0 then 1 else 0) - (if ℓ = -1 then 1 else 0)
    + π / 2 * (sgnHat ℓ - sgnHat (ℓ + 1)))

lemma two_add_pi_pos : 0 < 2 + π := by positivity

lemma sgnHat_one : sgnHat 1 = 2 / π := by
  rw [show (1 : ℤ) = 2 * 0 + 1 by norm_num, sgnHat_odd]
  simp [chat]

lemma sgnHat_neg_one : sgnHat (-1) = 2 / π := by
  rw [← sgnHat_neg, neg_neg, sgnHat_one]

lemma sgnHat_zero : sgnHat 0 = 0 := by simpa using sgnHat_two_mul 0

lemma psiHat_zero : psiHat 0 = 0 := by
  simp only [psiHat, if_true, show (0 : ℤ) = -1 ↔ False by norm_num, if_false, sub_zero,
    zero_add, sgnHat_zero, sgnHat_one]
  have hπ := pi_pos
  field_simp
  ring

lemma psiHat_neg_one : psiHat (-1) = 0 := by
  simp only [psiHat, show (-1 : ℤ) = 0 ↔ False by norm_num, if_false, if_true, zero_sub,
    neg_add_cancel, sgnHat_zero, sgnHat_neg_one]
  have hπ := pi_pos
  field_simp
  ring

/-- On the odd frequency `2j+1 ≠ −1`: `Ψ̂ = (2/(2+π))(−1)^j/(2j+1)`. -/
lemma psiHat_odd (j : ℤ) (hj : j ≠ -1) :
    psiHat (2 * j + 1) = 2 / (2 + π) * ((-1 : ℝ) ^ j / (2 * (j : ℝ) + 1)) := by
  have h0 : (2 * j + 1 ≠ 0) := by omega
  have h1 : (2 * j + 1 ≠ -1) := by omega
  simp only [psiHat, if_neg h0, if_neg h1, sub_zero, zero_add,
    show 2 * j + 1 + 1 = 2 * (j + 1) by ring, sgnHat_two_mul, sgnHat_odd, chat]
  have hπ := pi_pos
  field_simp

/-- On the even frequency `2j ≠ 0`: `Ψ̂ = −(2/(2+π))(−1)^j/(2j+1)`. -/
lemma psiHat_even (j : ℤ) (hj : j ≠ 0) :
    psiHat (2 * j) = -(2 / (2 + π) * ((-1 : ℝ) ^ j / (2 * (j : ℝ) + 1))) := by
  have h0 : (2 * j ≠ 0) := by omega
  have h1 : (2 * j ≠ -1) := by omega
  simp only [psiHat, if_neg h0, if_neg h1, sub_zero, zero_add, sgnHat_two_mul, sgnHat_odd, chat,
    zero_sub]
  have hπ := pi_pos
  field_simp

/-- `Ψ̂² = (4/(2+π)²)/(2j+1)²` on the pair `{2j, 2j+1}` (away from the heads). -/
lemma psiHat_sq_odd (j : ℤ) (hj : j ≠ -1) :
    psiHat (2 * j + 1) ^ 2 = 4 / (2 + π) ^ 2 * (1 / (2 * (j : ℝ) + 1) ^ 2) := by
  have h1 : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← sq_abs, abs_neg_one_zpow, one_pow]
  rw [psiHat_odd j hj, mul_pow, div_pow, div_pow, h1]
  ring

lemma psiHat_sq_even (j : ℤ) (hj : j ≠ 0) :
    psiHat (2 * j) ^ 2 = 4 / (2 + π) ^ 2 * (1 / (2 * (j : ℝ) + 1) ^ 2) := by
  have h1 : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← sq_abs, abs_neg_one_zpow, one_pow]
  rw [psiHat_even j hj, neg_sq, mul_pow, div_pow, div_pow, h1]
  ring

/-- The pair weight `w(2j) = w(2j+1) = 1/(2j+1)²`. -/
def pairW (ℓ : ℤ) : ℝ := 1 / (2 * ((ℓ / 2 : ℤ) : ℝ) + 1) ^ 2

lemma pairW_odd (j : ℤ) : pairW (2 * j + 1) = 1 / (2 * (j : ℝ) + 1) ^ 2 := by
  rw [pairW, show (2 * j + 1) / 2 = j by omega]

lemma pairW_even (j : ℤ) : pairW (2 * j) = 1 / (2 * (j : ℝ) + 1) ^ 2 := by
  rw [pairW, show (2 * j) / 2 = j by omega]

/-- `Ψ̂(ℓ)² ≤ (4/(2+π)²)·w(ℓ)` for every `ℓ` (equality off the heads, `0 ≤ ·` at them). -/
lemma psiHat_sq_le (ℓ : ℤ) : psiHat ℓ ^ 2 ≤ 4 / (2 + π) ^ 2 * pairW ℓ := by
  rcases Int.even_or_odd ℓ with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [← two_mul, pairW_even]
    by_cases hj : j = 0
    · subst hj
      rw [mul_zero, psiHat_zero, zero_pow two_ne_zero]
      positivity
    · rw [psiHat_sq_even j hj]
  · rw [pairW_odd]
    by_cases hj : j = -1
    · subst hj
      rw [show (2 : ℤ) * -1 + 1 = -1 by norm_num, psiHat_neg_one, zero_pow two_ne_zero]
      positivity
    · rw [psiHat_sq_odd j hj]

/-- `w(ℓ) ≤ 4/ℓ² + δ₀(ℓ)`: a summable majorant. -/
lemma pairW_le (ℓ : ℤ) : pairW ℓ ≤ 4 * (1 / (ℓ : ℝ) ^ 2) + (if ℓ = 0 then 1 else 0) := by
  rcases Int.even_or_odd ℓ with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [← two_mul, pairW_even]
    by_cases hj : j = 0
    · subst hj; norm_num
    · rw [if_neg (by omega)]
      have hj' : (1 : ℝ) ≤ |(j : ℝ)| := by
        have : (1 : ℤ) ≤ |j| := Int.one_le_abs hj
        exact_mod_cast this
      have h1 : (0 : ℝ) < (2 * (j : ℝ) + 1) ^ 2 := by
        have : (2 * j + 1 : ℤ) ≠ 0 := by omega
        have : (2 * (j : ℝ) + 1) ≠ 0 := by exact_mod_cast this
        positivity
      have h2 : (0 : ℝ) < (2 * (j : ℝ)) ^ 2 := by
        have : (2 * (j : ℝ)) ≠ 0 := by exact_mod_cast (show (2 * j : ℤ) ≠ 0 by omega)
        positivity
      push_cast
      rw [add_zero, mul_one_div, div_le_div_iff₀ h1 h2]
      -- `(2j)² ≤ 4(2j+1)²`, i.e. `j² ≤ (2j+1)²` for `|j| ≥ 1`
      rcases le_or_gt 1 j with hj1 | hj1
      · have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
        nlinarith
      · have : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
        nlinarith [mul_nonneg_of_nonpos_of_nonpos (by linarith : 3 * (j : ℝ) + 1 ≤ 0)
          (by linarith : (j : ℝ) + 1 ≤ 0)]
  · rw [pairW_odd, if_neg (by omega)]
    have h1 : (0 : ℝ) < (2 * (j : ℝ) + 1) ^ 2 := by
      have : (2 * j + 1 : ℤ) ≠ 0 := by omega
      have : (2 * (j : ℝ) + 1) ≠ 0 := by exact_mod_cast this
      positivity
    push_cast
    rw [add_zero]
    have hx : (0 : ℝ) ≤ 1 / (2 * (j : ℝ) + 1) ^ 2 := by positivity
    linarith

lemma summable_pairW : Summable pairW := by
  have h1 : Summable fun ℓ : ℤ => 4 * (1 / (ℓ : ℝ) ^ 2) :=
    ((Real.summable_one_div_int_pow).mpr (by norm_num : 1 < 2)).mul_left _
  have h2 : Summable fun ℓ : ℤ => (if ℓ = 0 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) fun ℓ hℓ => by
      simp only [Finset.mem_singleton] at hℓ; simp [hℓ]
  exact (h1.add h2).of_nonneg_of_le (fun ℓ => by unfold pairW; positivity) pairW_le

/-- `∑_ℓ w(ℓ) = 2·(π²/4) = π²/2`. -/
lemma tsum_pairW : ∑' ℓ : ℤ, pairW ℓ = π ^ 2 / 2 := by
  rw [KsIndex.GammaOne.tsum_int_even_add_odd summable_pairW]
  have hodd : HasSum (fun j : ℤ => 1 / (2 * (j : ℝ) + 1) ^ 2) (π ^ 2 / 4) :=
    hasSum_int_odd_sq_inv
  have hE : ∑' n : ℤ, pairW (2 * n) = π ^ 2 / 4 := by
    rw [← hodd.tsum_eq]; exact tsum_congr fun n => pairW_even n
  have hO : ∑' n : ℤ, pairW (2 * n + 1) = π ^ 2 / 4 := by
    rw [← hodd.tsum_eq]; exact tsum_congr fun n => pairW_odd n
  rw [hE, hO]; ring

lemma hasSum_pairW : HasSum pairW (π ^ 2 / 2) := tsum_pairW ▸ summable_pairW.hasSum


lemma summable_psiHat_sq : Summable fun ℓ : ℤ => psiHat ℓ ^ 2 :=
  (summable_pairW.mul_left _).of_nonneg_of_le (fun _ => sq_nonneg _) psiHat_sq_le

/-! ### The `Ψ` identity -/

lemma summable_sgnHat_mul {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) :
    Summable fun ℓ : ℤ => (sgnHat ℓ : ℂ) * u ℓ :=
  (summable_convS₁_term hu 0).congr fun ℓ => by rw [zero_sub, sgnHat_neg]

lemma summable_sgnHat_succ_mul {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) :
    Summable fun ℓ : ℤ => (sgnHat (ℓ + 1) : ℂ) * u ℓ :=
  (summable_convS₁_term hu (-1)).congr fun ℓ => by
    rw [show (-1 : ℤ) - ℓ = -(ℓ + 1) by ring, sgnHat_neg]

lemma summable_delta_mul (u : ℤ → ℂ) (ℓ₀ : ℤ) :
    Summable fun ℓ : ℤ => ((if ℓ = ℓ₀ then (1 : ℝ) else 0 : ℝ) : ℂ) * u ℓ :=
  summable_of_ne_finset_zero (s := {ℓ₀}) fun ℓ hℓ => by
    simp only [Finset.mem_singleton] at hℓ; simp [hℓ]

lemma tsum_delta_mul (u : ℤ → ℂ) (ℓ₀ : ℤ) :
    ∑' ℓ : ℤ, ((if ℓ = ℓ₀ then (1 : ℝ) else 0 : ℝ) : ℂ) * u ℓ = u ℓ₀ := by
  rw [tsum_eq_single ℓ₀ (fun ℓ hℓ => by simp [hℓ])]
  simp

/-- The summand `Ψ̂(ℓ)u(ℓ)` as a combination of the four elementary families. -/
lemma psiHat_mul_eq (u : ℤ → ℂ) (ℓ : ℤ) :
    (psiHat ℓ : ℂ) * u ℓ
      = ((2 / (2 + π) : ℝ) : ℂ) *
        ((((if ℓ = 0 then (1 : ℝ) else 0 : ℝ) : ℂ) * u ℓ
          - ((if ℓ = -1 then (1 : ℝ) else 0 : ℝ) : ℂ) * u ℓ)
          + ((π / 2 : ℝ) : ℂ) * ((sgnHat ℓ : ℂ) * u ℓ - (sgnHat (ℓ + 1) : ℂ) * u ℓ)) := by
  simp only [psiHat]
  push_cast
  ring

lemma summable_psiHat_mul {u : ℤ → ℂ} (hu : Summable fun n : ℤ => ‖u n‖ ^ 2) :
    Summable fun ℓ : ℤ => (psiHat ℓ : ℂ) * u ℓ := by
  refine (Summable.congr ?_ fun ℓ => (psiHat_mul_eq u ℓ).symm)
  exact ((((summable_delta_mul u 0).sub (summable_delta_mul u (-1))).add
    (((summable_sgnHat_mul hu).sub (summable_sgnHat_succ_mul hu)).mul_left _)).mul_left _)

/-- **The `Ψ` identity**: `∑ Ψ̂(ℓ) u(ℓ) = u(0) − u(−1)` for arc-supported `u`
(paper: `⟨Ψ,u⟩ = 2π(û(0)−û(−1))`, "using `supp u ⊆ closure(arc)`"). -/
theorem tsum_psiHat_mul {u : ℤ → ℂ} (hu : u ∈ ArcDom) :
    ∑' ℓ : ℤ, (psiHat ℓ : ℂ) * u ℓ = u 0 - u (-1) := by
  have hsq := hu.summable_sq
  rw [tsum_congr fun ℓ => psiHat_mul_eq u ℓ, tsum_mul_left,
    ((summable_delta_mul u 0).sub (summable_delta_mul u (-1))).tsum_add
      (((summable_sgnHat_mul hsq).sub (summable_sgnHat_succ_mul hsq)).mul_left _),
    (summable_delta_mul u 0).tsum_sub (summable_delta_mul u (-1)), tsum_mul_left,
    (summable_sgnHat_mul hsq).tsum_sub (summable_sgnHat_succ_mul hsq),
    tsum_delta_mul, tsum_delta_mul, tsum_sgnHat_mul hu, tsum_sgnHat_succ_mul hu]
  have hπ : (2 + π : ℝ) ≠ 0 := two_add_pi_pos.ne'
  have key : ((2 / (2 + π) : ℝ) : ℂ) * (1 + ((π / 2 : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_mul]
    congr 1
    field_simp
  linear_combination (u 0 - u (-1)) * key

/-! ### Cauchy–Schwarz -/

/-- `Sconst(a,b) = ∑_{ℓ ≠ 0,−1} Ψ̂(ℓ)²/σ_{(a;k)}(ℓ)`. -/
def Sconst (a b : ℝ) : ℝ :=
  ∑' ℓ : ℤ, (if ℓ = 0 ∨ ℓ = -1 then 0 else psiHat ℓ ^ 2 / sigmaArc a b ℓ)

/-- Off the heads `σ ≥ min(a, 1−a)` when `|b| ≤ 1`. -/
lemma sigmaArc_tail_ge (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| ≤ 1) {ℓ : ℤ}
    (h0 : ℓ ≠ 0) (h1 : ℓ ≠ -1) : min a (1 - a) ≤ sigmaArc a b ℓ := by
  set m := min a (1 - a) with hm
  have hm0 : 0 < m := lt_min ha.1 (by linarith [ha.2])
  have hm1 : m ≤ a := min_le_left _ _
  have hm2 : m ≤ 1 - a := min_le_right _ _
  have hge : 1 + m ≤ |(ℓ : ℝ) + a| := by
    rcases le_or_gt 0 ℓ with h | h
    · have : (1 : ℝ) ≤ ℓ := by exact_mod_cast (show 1 ≤ ℓ by omega)
      rw [abs_of_pos (by linarith [ha.1])]; linarith
    · have : (ℓ : ℝ) ≤ -2 := by exact_mod_cast (show ℓ ≤ -2 by omega)
      rw [abs_of_neg (by linarith [ha.2])]; linarith
  have hpos := abs_add_pos ha ℓ
  have hb2 : b ^ 2 ≤ 1 := by nlinarith [abs_nonneg b, sq_abs b]
  rw [sigmaArc_eq ha]
  have h1' : b ^ 2 / |(ℓ : ℝ) + a| ≤ 1 / |(ℓ : ℝ) + a| :=
    div_le_div_of_nonneg_right hb2 hpos.le
  have h2 : 1 / |(ℓ : ℝ) + a| ≤ 1 / (1 + m) :=
    one_div_le_one_div_of_le (by linarith) hge
  have h3 : 1 / (1 + m) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  linarith

/-- The tail quotients `Ψ̂²/σ` are summable (`σ ≥ min(a,1−a)` off the heads). -/
lemma summable_Sconst_term (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| ≤ 1) :
    Summable fun ℓ : ℤ => (if ℓ = 0 ∨ ℓ = -1 then 0 else psiHat ℓ ^ 2 / sigmaArc a b ℓ) := by
  have hm0 : 0 < min a (1 - a) := lt_min ha.1 (by linarith [ha.2])
  refine (summable_psiHat_sq.mul_left (1 / min a (1 - a))).of_nonneg_of_le
    (fun ℓ => ?_) fun ℓ => ?_
  · split_ifs with h
    · exact le_rfl
    · push Not at h
      exact div_nonneg (sq_nonneg _) (le_trans hm0.le (sigmaArc_tail_ge ha hb h.1 h.2))
  · split_ifs with h
    · positivity
    · push Not at h
      have hs := sigmaArc_tail_ge ha hb h.1 h.2
      rw [div_le_iff₀ (lt_of_lt_of_le hm0 hs), one_div_mul_eq_div, div_mul_eq_mul_div,
        le_div_iff₀ hm0]
      nlinarith [sq_nonneg (psiHat ℓ)]

lemma Sconst_nonneg (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| ≤ 1) : 0 ≤ Sconst a b := by
  refine tsum_nonneg fun ℓ => ?_
  have hm0 : 0 < min a (1 - a) := lt_min ha.1 (by linarith [ha.2])
  split_ifs with h
  · exact le_rfl
  · push Not at h
    exact div_nonneg (sq_nonneg _) (le_trans hm0.le (sigmaArc_tail_ge ha hb h.1 h.2))

/-- **Cauchy–Schwarz**: `|u(0) − u(−1)|² ≤ Sconst · tail(u)` for
`u ∈ ArcDom`, `0 < a < 1` and `|b| < 1`. -/
theorem head_diff_sq_le (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| < 1) {u : ℤ → ℂ}
    (hu : u ∈ ArcDom) :
    ‖u 0 - u (-1)‖ ^ 2 ≤ Sconst a b * ∑' ℓ : ℤ, tailTerm a b u ℓ := by
  have hsq := hu.summable_sq
  have hm0 : 0 < min a (1 - a) := lt_min ha.1 (by linarith [ha.2])
  -- the two real factor sequences
  set p : ℤ → ℝ := fun ℓ =>
    if ℓ = 0 ∨ ℓ = -1 then 0 else |psiHat ℓ| / Real.sqrt (sigmaArc a b ℓ) with hp
  set q : ℤ → ℝ := fun ℓ =>
    if ℓ = 0 ∨ ℓ = -1 then 0 else Real.sqrt (sigmaArc a b ℓ) * ‖u ℓ‖ with hq
  have hσpos : ∀ ℓ : ℤ, ¬ (ℓ = 0 ∨ ℓ = -1) → 0 < sigmaArc a b ℓ := by
    intro ℓ h
    push Not at h
    exact sigmaArc_pos ha hb h.1 h.2
  have hpq : ∀ ℓ, p ℓ * q ℓ = |psiHat ℓ| * ‖u ℓ‖ := by
    intro ℓ
    simp only [hp, hq]
    split_ifs with h
    · rcases h with rfl | rfl
      · simp [psiHat_zero]
      · simp [psiHat_neg_one]
    · have hs := hσpos ℓ h
      have hsq' : Real.sqrt (sigmaArc a b ℓ) ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
      field_simp
  have hp2 : ∀ ℓ, p ℓ ^ 2 = if ℓ = 0 ∨ ℓ = -1 then 0 else psiHat ℓ ^ 2 / sigmaArc a b ℓ := by
    intro ℓ
    simp only [hp]
    split_ifs with h
    · simp
    · rw [div_pow, sq_abs, Real.sq_sqrt (hσpos ℓ h).le]
  have hq2 : ∀ ℓ, q ℓ ^ 2 = tailTerm a b u ℓ := by
    intro ℓ
    simp only [hq, tailTerm]
    split_ifs with h
    · simp
    · rw [mul_pow, Real.sq_sqrt (hσpos ℓ h).le]
  have hpsum : Summable fun ℓ => p ℓ ^ 2 := by
    simp only [hp2]; exact summable_Sconst_term ha hb.le
  have hqsum : Summable fun ℓ => q ℓ ^ 2 := by
    simp only [hq2]; exact summable_tailTerm ha b hu.1
  have hnorm : Summable fun ℓ : ℤ => ‖(psiHat ℓ : ℂ) * u ℓ‖ := by
    refine (summable_mul_of_sq hpsum hqsum).congr fun ℓ => ?_
    rw [hpq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖u 0 - u (-1)‖ ≤ ∑' ℓ : ℤ, p ℓ * q ℓ := by
    rw [← tsum_psiHat_mul hu]
    refine le_trans (norm_tsum_le_tsum_norm hnorm) (le_of_eq (tsum_congr fun ℓ => ?_))
    rw [hpq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 := tsum_mul_sq_le hpsum hqsum
  have h0 : 0 ≤ ∑' ℓ : ℤ, p ℓ * q ℓ :=
    tsum_nonneg fun ℓ => by rw [hpq]; positivity
  calc ‖u 0 - u (-1)‖ ^ 2 ≤ (∑' ℓ : ℤ, p ℓ * q ℓ) ^ 2 := by gcongr
    _ ≤ (∑' ℓ : ℤ, p ℓ ^ 2) * ∑' ℓ : ℤ, q ℓ ^ 2 := h2
    _ = Sconst a b * ∑' ℓ : ℤ, tailTerm a b u ℓ := by
      rw [Sconst]
      congr 1
      · exact tsum_congr hp2
      · exact tsum_congr hq2

end KsIndex.ArcPsi
