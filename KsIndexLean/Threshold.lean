module

/-
The least-value function `γ` is strictly increasing on `(0,∞)` and positive
at `√3`, as in [ksindexi], `single_crossing` and `threshold_upper_bound`.

Both arguments use the coefficient isometry `S = convS` and its inverse
from `SIsometry`. Strict monotonicity follows by comparing a minimizer at
the larger parameter with the same vector at the smaller parameter. The
minus-lattice energy is strictly positive: its only zero mode would force
the original vector outside the half-order Sobolev domain.

For `γ(√3) > 0`, a momentum estimate isolates the exceptional physical
frequency `-2` (coefficient index `-1`). Weighted Cauchy–Schwarz with weight
`sigP + 9` gives a uniform lower bound on normalized domain vectors. The
constant is positive because `9 * ∑ Aweight < 1`, proved using Parseval and
the positive eight-term rational sum `88090307/313283512080`, with all omitted
terms nonnegative. Passing this uniform bound to the infimum avoids choosing
an eigenfunction for the upper-threshold argument.
-/
public import KsIndexLean.CircleQ
public import KsIndexLean.SIsometry

@[expose] public section


noncomputable section

namespace KsIndex.Threshold

open KsIndex.CircleQ KsIndex.SIsometry Real Filter Topology

/-! ### The Cauchy–Schwarz weight `σ₃ + 9` -/

/-- The shifted symbol `σ₃(6n+1) + 9`, strictly positive (`≥ 6`). -/
def sigP9 (n : ℤ) : ℝ := sigP n + 9

lemma sigP9_ge_six (n : ℤ) : 6 ≤ sigP9 n := by
  have := sigP_ge_neg_three n; rw [sigP9]; linarith

lemma sigP9_pos (n : ℤ) : 0 < sigP9 n := lt_of_lt_of_le (by norm_num) (sigP9_ge_six n)

/-- The Cauchy–Schwarz weight `chat(-1-n)² / (σ₃(6n+1)+9)`.
Here `chat(-1-n)` is the sign-multiplier coefficient at physical frequency
`-6n-3`, coupling input frequency `6n+1` to output frequency `-2`. -/
def Aweight (n : ℤ) : ℝ := chat (-1 - n) ^ 2 / sigP9 n

/-- The `B`-summand `(σ₃+9)‖u‖²` (the CS energy). -/
def Bweight (u : ℤ → ℂ) (n : ℤ) : ℝ := sigP9 n * ‖u n‖ ^ 2

lemma Aweight_nonneg (n : ℤ) : 0 ≤ Aweight n :=
  div_nonneg (sq_nonneg _) (sigP9_pos n).le

lemma summable_chat_neg_one_sub_sq : Summable fun n : ℤ => chat (-1 - n) ^ 2 := by
  have hinj : Function.Injective (fun n : ℤ => -1 - n) := fun a b hab => by
    simp only at hab; omega
  exact (summable_chat_sq.comp_injective hinj).congr fun n => rfl

lemma summable_Aweight : Summable Aweight := by
  refine (summable_chat_neg_one_sub_sq.mul_left (1 / 6)).of_nonneg_of_le
    (fun n => Aweight_nonneg n) fun n => ?_
  rw [Aweight, div_le_iff₀ (sigP9_pos n)]
  have h6 := sigP9_ge_six n
  nlinarith [sq_nonneg (chat (-1 - n)), sigP9_pos n]

lemma summable_Bweight {u : ℤ → ℂ} (hu : MemDom u) : Summable (Bweight u) := by
  have h : Summable fun n : ℤ => sigP n * ‖u n‖ ^ 2 + 9 * ‖u n‖ ^ 2 :=
    (summable_sigP_mul hu.1).add ((summable_normSq hu.1).mul_left 9)
  exact h.congr fun n => by rw [Bweight, sigP9]; ring

/-! ### The rational-series machinery for `9A < 1` -/

/-- The `π`-free rescaling of `Aweight`: `Aweight = (4/π²)·Aterm`. -/
def Aterm (n : ℤ) : ℝ := 1 / ((2 * (n : ℝ) + 1) ^ 2 * sigP9 n)

/-- The denominator bracket `|6n+1|(|6n+1|+9) − 4`. -/
def brn (n : ℤ) : ℝ := |6 * (n : ℝ) + 1| * (|6 * (n : ℝ) + 1| + 9) - 4

/-- The combined summand `1/(6n+3)² − Aterm`, whose sum is `(π²/36)(1−S)`. -/
def term (n : ℤ) : ℝ := 1 / (6 * (n : ℝ) + 3) ^ 2 - Aterm n

lemma brn_pos (n : ℤ) : 0 < brn n := by
  have hL := abs_freqP_ge_one n
  rw [brn]; nlinarith [hL]

lemma Aweight_eq (n : ℤ) : Aweight n = (4 / π ^ 2) * Aterm n := by
  have hchat : chat (-1 - n) ^ 2 = 4 / π ^ 2 / (2 * (n : ℝ) + 1) ^ 2 := by
    rw [chat_sq, show (2 * (((-1 - n : ℤ)) : ℝ) + 1) ^ 2 = (2 * (n : ℝ) + 1) ^ 2 from by
      push_cast; ring]
  have hπ : π ^ 2 ≠ 0 := pow_ne_zero 2 pi_ne_zero
  have h21 : (2 * (n : ℝ) + 1) ^ 2 ≠ 0 := pow_ne_zero 2 (two_mul_add_one_ne_zero n)
  rw [Aweight, Aterm, hchat]
  field_simp

/-- Square-summability transfer: `Aterm` is summable. -/
lemma summable_Aterm : Summable Aterm := by
  have hπ : (4 / π ^ 2) ≠ 0 := by positivity
  have h := summable_Aweight.mul_left (π ^ 2 / 4)
  refine h.congr fun n => ?_
  rw [Aweight_eq]
  have : π ^ 2 ≠ 0 := pow_ne_zero 2 pi_ne_zero
  field_simp

/-- `σ₃+9 = brn/|6n+1|`. -/
lemma sigP9_eq_brn (n : ℤ) : sigP9 n = brn n / |6 * (n : ℝ) + 1| := by
  have hLge : (1 : ℝ) ≤ |6 * (n : ℝ) + 1| := abs_freqP_ge_one n
  have hLne : |6 * (n : ℝ) + 1| ≠ 0 := by intro h; rw [h] at hLge; linarith
  rw [sigP9, sigP, brn, ← sq_abs (6 * (n : ℝ) + 1)]
  field_simp
  ring

/-- `Aterm = |6n+1| / ((2n+1)²·brn)` — no nested `sigP` fraction. -/
lemma Aterm_eq (n : ℤ) :
    Aterm n = |6 * (n : ℝ) + 1| / ((2 * (n : ℝ) + 1) ^ 2 * brn n) := by
  have h21 : (2 * (n : ℝ) + 1) ^ 2 ≠ 0 := pow_ne_zero 2 (two_mul_add_one_ne_zero n)
  have hbrne : brn n ≠ 0 := ne_of_gt (brn_pos n)
  have hLge : (1 : ℝ) ≤ |6 * (n : ℝ) + 1| := abs_freqP_ge_one n
  have hLne : |6 * (n : ℝ) + 1| ≠ 0 := by intro h; rw [h] at hLge; linarith
  rw [Aterm, sigP9_eq_brn]
  field_simp

/-- The two forms of the summand agree. -/
lemma term_eq (n : ℤ) :
    term n = (6 * (n : ℝ) - 1) / ((6 * (n : ℝ) + 3) * brn n) := by
  have h21 : (2 * (n : ℝ) + 1) ≠ 0 := two_mul_add_one_ne_zero n
  have h63 : (6 * (n : ℝ) + 3) ≠ 0 := by
    rw [show 6 * (n : ℝ) + 3 = 3 * (2 * (n : ℝ) + 1) from by ring]
    exact mul_ne_zero (by norm_num) h21
  have hbrne : brn n ≠ 0 := ne_of_gt (brn_pos n)
  have hbrL : brn n = |6 * (n : ℝ) + 1| ^ 2 + 9 * |6 * (n : ℝ) + 1| - 4 := by
    rw [brn]; ring
  rw [term, Aterm_eq]
  rw [div_sub_div _ _ (pow_ne_zero 2 h63) (mul_ne_zero (pow_ne_zero 2 h21) hbrne),
    div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 h63) (mul_ne_zero (pow_ne_zero 2 h21) hbrne))
      (mul_ne_zero h63 hbrne)]
  rw [hbrL]
  rcases le_or_gt 0 n with hn | hn
  · have hpos : (0 : ℝ) ≤ 6 * (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [abs_of_nonneg hpos]; ring
  · have hneg : 6 * (n : ℝ) + 1 < 0 := by
      have : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
      linarith
    rw [abs_of_neg hneg]; ring

/-! ### The momentum / isometry bound -/

/-- `3(‖u‖² − |convS u(−1)|²) ≤ ⟨N₃⁻ςu, ςu⟩`: `σ₃ ≥ 3` off its zero at
`ℓ = −2` (`m = −1`), and the isometry supplies `∑‖convS u‖² = ‖u‖²`. -/
lemma momentum_bound {u : ℤ → ℂ} (hu : MemDom u) :
    3 * (normSq u - ‖convS u (-1)‖ ^ 2) ≤ ∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2 := by
  have hiso : ∑' m : ℤ, ‖convS u m‖ ^ 2 = normSq u := tsum_convS_sq_eq_normSq hu
  have hSsum : Summable fun m : ℤ => ‖convS u m‖ ^ 2 :=
    summable_convS_sq (summable_normSq hu.1)
  have hsigMsum : Summable fun m : ℤ => sigM m * ‖convS u m‖ ^ 2 :=
    summable_sigM_mul hu.2
  have hind_sum : Summable fun m : ℤ => (if m = -1 then ‖convS u m‖ ^ 2 else 0) :=
    summable_of_ne_finset_zero (s := {(-1 : ℤ)})
      fun m hm => if_neg (by simpa using hm)
  have hind_val : (∑' m : ℤ, if m = -1 then ‖convS u m‖ ^ 2 else 0)
      = ‖convS u (-1)‖ ^ 2 := by
    rw [tsum_eq_single (-1) fun m hm => if_neg hm, if_pos rfl]
  have hlhs_sum : Summable fun m : ℤ =>
      3 * ‖convS u m‖ ^ 2 - 3 * (if m = -1 then ‖convS u m‖ ^ 2 else 0) :=
    (hSsum.mul_left 3).sub (hind_sum.mul_left 3)
  have hpt : ∀ m : ℤ, 3 * ‖convS u m‖ ^ 2
      - 3 * (if m = -1 then ‖convS u m‖ ^ 2 else 0) ≤ sigM m * ‖convS u m‖ ^ 2 := by
    intro m
    by_cases hm : m = -1
    · subst hm; rw [if_pos rfl, sigM_neg_one, zero_mul]; linarith
    · rw [if_neg hm]
      have h3 : (3 : ℝ) ≤ sigM m := sigM_ge_three_of_ne hm
      nlinarith [sq_nonneg ‖convS u m‖]
  have hle := hlhs_sum.tsum_le_tsum hpt hsigMsum
  rw [(hSsum.mul_left 3).tsum_sub (hind_sum.mul_left 3), tsum_mul_left,
    tsum_mul_left, hiso, hind_val] at hle
  linarith

/-! ### The Cauchy–Schwarz bound -/

/-- `|convS u(−1)|² ≤ (∑ A)·(∑ B)` — Cauchy–Schwarz against the weight
`σ₃+9`, split as `ς̂/√(σ₃+9)` times `√(σ₃+9)·û`. -/
lemma norm_convS_neg_one_sq_le {u : ℤ → ℂ} (hu : MemDom u) :
    ‖convS u (-1)‖ ^ 2 ≤ (∑' n : ℤ, Aweight n) * (∑' n : ℤ, Bweight u n) := by
  set p : ℤ → ℝ := fun n => |chat (-1 - n)| * (Real.sqrt (sigP9 n))⁻¹ with hp
  set q : ℤ → ℝ := fun n => Real.sqrt (sigP9 n) * ‖u n‖ with hq
  have hsne : ∀ n : ℤ, Real.sqrt (sigP9 n) ≠ 0 := fun n =>
    Real.sqrt_ne_zero'.mpr (sigP9_pos n)
  have hp2 : ∀ n : ℤ, p n ^ 2 = Aweight n := by
    intro n
    rw [hp, mul_pow, inv_pow, Real.sq_sqrt (sigP9_pos n).le, sq_abs, Aweight,
      div_eq_mul_inv]
  have hq2 : ∀ n : ℤ, q n ^ 2 = Bweight u n := by
    intro n
    rw [hq, mul_pow, Real.sq_sqrt (sigP9_pos n).le, Bweight]
  have hpq : ∀ n : ℤ, p n * q n = |chat (-1 - n)| * ‖u n‖ := by
    intro n
    have hcancel : (Real.sqrt (sigP9 n))⁻¹ * Real.sqrt (sigP9 n) = 1 :=
      inv_mul_cancel₀ (hsne n)
    rw [hp, hq]
    calc |chat (-1 - n)| * (Real.sqrt (sigP9 n))⁻¹ * (Real.sqrt (sigP9 n) * ‖u n‖)
        = |chat (-1 - n)| * ‖u n‖
          * ((Real.sqrt (sigP9 n))⁻¹ * Real.sqrt (sigP9 n)) := by ring
      _ = |chat (-1 - n)| * ‖u n‖ := by rw [hcancel, mul_one]
  have hpsum : Summable fun n : ℤ => p n ^ 2 :=
    summable_Aweight.congr fun n => (hp2 n).symm
  have hqsum : Summable fun n : ℤ => q n ^ 2 :=
    (summable_Bweight hu).congr fun n => (hq2 n).symm
  have hpqsum : Summable fun n : ℤ => p n * q n := summable_mul_of_sq hpsum hqsum
  have hnormsum : Summable fun n : ℤ => ‖(chat (-1 - n) : ℂ) * u n‖ :=
    hpqsum.congr fun n => by
      rw [hpq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hb1 : ‖convS u (-1)‖ ≤ ∑' n : ℤ, p n * q n := by
    have hconv : convS u (-1) = ∑' n : ℤ, (chat (-1 - n) : ℂ) * u n := rfl
    rw [hconv]
    exact (norm_tsum_le_tsum_norm hnormsum).trans_eq
      (tsum_congr fun n => by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hpq])
  have hb1sq : ‖convS u (-1)‖ ^ 2 ≤ (∑' n : ℤ, p n * q n) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb1 2
  calc ‖convS u (-1)‖ ^ 2 ≤ (∑' n : ℤ, p n * q n) ^ 2 := hb1sq
    _ ≤ (∑' n : ℤ, p n ^ 2) * ∑' n : ℤ, q n ^ 2 := tsum_mul_sq_le hpsum hqsum
    _ = (∑' n : ℤ, Aweight n) * ∑' n : ℤ, Bweight u n := by
        rw [tsum_congr hp2, tsum_congr hq2]

/-! ### The strict inequality `9A < 1` -/

lemma summable_term : Summable term :=
  (hasSum_int_six_shift_sq_inv.summable.sub summable_Aterm)

/-- Off the window `[−4,3]`, every summand is nonnegative. -/
lemma term_nonneg_of_notMem {n : ℤ} (hn : n ∉ Finset.Icc (-4 : ℤ) 3) :
    0 ≤ term n := by
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  rw [term_eq]
  have hbr := brn_pos n
  rcases hn with hlt | hgt
  · have hn5 : (n : ℝ) ≤ -5 := by exact_mod_cast (show n ≤ -5 by omega)
    have h1 : 6 * (n : ℝ) - 1 ≤ 0 := by linarith
    have h2 : (6 * (n : ℝ) + 3) * brn n ≤ 0 :=
      mul_nonpos_iff.mpr (Or.inr ⟨by linarith, hbr.le⟩)
    exact div_nonneg_iff.mpr (Or.inr ⟨h1, h2⟩)
  · have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 4 ≤ n by omega)
    have h1 : 0 ≤ 6 * (n : ℝ) - 1 := by linarith
    have h2 : 0 ≤ (6 * (n : ℝ) + 3) * brn n := mul_nonneg (by linarith) hbr.le
    exact div_nonneg h1 h2

/-- The eight-term partial sum over `[−4,3]`. -/
lemma term_partial_sum :
    ∑ n ∈ Finset.Icc (-4 : ℤ) 3, term n = (88090307 : ℝ) / 313283512080 := by
  rw [show (Finset.Icc (-4 : ℤ) 3) = {-4, -3, -2, -1, 0, 1, 2, 3} from by decide,
    Finset.sum_insert (by decide : (-4 : ℤ) ∉ ({-3, -2, -1, 0, 1, 2, 3} : Finset ℤ)),
    Finset.sum_insert (by decide : (-3 : ℤ) ∉ ({-2, -1, 0, 1, 2, 3} : Finset ℤ)),
    Finset.sum_insert (by decide : (-2 : ℤ) ∉ ({-1, 0, 1, 2, 3} : Finset ℤ)),
    Finset.sum_insert (by decide : (-1 : ℤ) ∉ ({0, 1, 2, 3} : Finset ℤ)),
    Finset.sum_insert (by decide : (0 : ℤ) ∉ ({1, 2, 3} : Finset ℤ)),
    Finset.sum_insert (by decide : (1 : ℤ) ∉ ({2, 3} : Finset ℤ)),
    Finset.sum_insert (by decide : (2 : ℤ) ∉ ({3} : Finset ℤ)),
    Finset.sum_singleton]
  simp only [term_eq, brn]
  norm_num

/-- `S = 9·∑ ς̂(−1−n)²/(σ₃+9) < 1`.  (Proved via the Parseval identity and
the positive rational partial sum `88090307/313283512080`.) -/
theorem nine_A_lt_one : 9 * ∑' n : ℤ, Aweight n < 1 := by
  have hπpos : (0 : ℝ) < π ^ 2 := by positivity
  have hAsum : (∑' n : ℤ, Aweight n) = (4 / π ^ 2) * ∑' n : ℤ, Aterm n := by
    rw [← tsum_mul_left]; exact tsum_congr Aweight_eq
  have hParseval : (∑' n : ℤ, 1 / (6 * (n : ℝ) + 3) ^ 2) = π ^ 2 / 36 :=
    hasSum_int_six_shift_sq_inv.tsum_eq
  have htsum : (∑' n : ℤ, term n) = π ^ 2 / 36 - ∑' n : ℤ, Aterm n := by
    have : (∑' n : ℤ, term n) = ∑' n : ℤ, (1 / (6 * (n : ℝ) + 3) ^ 2 - Aterm n) := rfl
    rw [this, hasSum_int_six_shift_sq_inv.summable.tsum_sub summable_Aterm, hParseval]
  have hge : (88090307 : ℝ) / 313283512080 ≤ ∑' n : ℤ, term n := by
    calc (88090307 : ℝ) / 313283512080
        = ∑ n ∈ Finset.Icc (-4 : ℤ) 3, term n := term_partial_sum.symm
      _ ≤ ∑' n : ℤ, term n :=
          summable_term.sum_le_tsum _ fun n hn => term_nonneg_of_notMem hn
  have htermpos : 0 < ∑' n : ℤ, term n := lt_of_lt_of_le (by norm_num) hge
  have hAtermlt : (∑' n : ℤ, Aterm n) < π ^ 2 / 36 := by rw [htsum] at htermpos; linarith
  rw [hAsum, show 9 * (4 / π ^ 2 * ∑' n : ℤ, Aterm n) = (36 / π ^ 2) * ∑' n : ℤ, Aterm n from by
    ring, show (1 : ℝ) = (36 / π ^ 2) * (π ^ 2 / 36) from by field_simp]
  exact mul_lt_mul_of_pos_left hAtermlt (by positivity)

/-- `6‖u‖² ≤ ∑ B`: the CS energy dominates `6‖u‖²` since `σ₃+9 ≥ 6`. -/
lemma Bweight_ge {u : ℤ → ℂ} (hu : MemDom u) :
    6 * normSq u ≤ ∑' n : ℤ, Bweight u n := by
  have hpt : ∀ n : ℤ, 6 * ‖u n‖ ^ 2 ≤ Bweight u n := fun n => by
    rw [Bweight]; nlinarith [sigP9_ge_six n, sq_nonneg ‖u n‖]
  have h6sum : Summable fun n : ℤ => 6 * ‖u n‖ ^ 2 := (summable_normSq hu.1).mul_left 6
  have hle := h6sum.tsum_le_tsum hpt (summable_Bweight hu)
  rw [tsum_mul_left] at hle
  exact hle

/-- The per-`u` lower bound `(1−9A)·∑B ≤ Q_{√3}(u)`. -/
lemma qform_sqrt_three_lb {u : ℤ → ℂ} (hu : MemDom u) :
    (1 - 9 * ∑' n : ℤ, Aweight n) * (∑' n : ℤ, Bweight u n)
      ≤ Qform (Real.sqrt 3) u := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hmom := momentum_bound hu
  have hcs := norm_convS_neg_one_sq_le hu
  have hBsplit : (∑' n : ℤ, Bweight u n)
      = (∑' n : ℤ, sigP n * ‖u n‖ ^ 2) + 9 * normSq u := by
    rw [normSq, ← tsum_mul_left,
      ← (summable_sigP_mul hu.1).tsum_add ((summable_normSq hu.1).mul_left 9)]
    exact tsum_congr fun n => by rw [Bweight, sigP9]; ring
  have key : (1 - 9 * ∑' n : ℤ, Aweight n) * (∑' n : ℤ, Bweight u n)
      = (∑' n : ℤ, Bweight u n)
        - 9 * ((∑' n : ℤ, Aweight n) * (∑' n : ℤ, Bweight u n)) := by ring
  rw [Qform, h3, key]
  linarith [hmom, hcs, hBsplit]

/-- **Paper's `threshold_upper_bound`: `γ(√3) > 0`.** -/
theorem gam_sqrt_three_pos : 0 < gam (Real.sqrt 3) := by
  have hA1 := nine_A_lt_one
  have h19 : 0 < 1 - 9 * ∑' n : ℤ, Aweight n := by linarith
  set c : ℝ := 6 * (1 - 9 * ∑' n : ℤ, Aweight n) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hlb : ∀ u : ℤ → ℂ, MemDom u → normSq u = 1 → c ≤ Qform (Real.sqrt 3) u := by
    intro u hu hn
    have h1 := qform_sqrt_three_lb hu
    have h2 := Bweight_ge hu
    rw [hn, mul_one] at h2
    have hchain : c ≤ (1 - 9 * ∑' n : ℤ, Aweight n) * (∑' n : ℤ, Bweight u n) := by
      rw [hc, mul_comm]
      exact mul_le_mul_of_nonneg_left h2 h19.le
    linarith
  rw [gam]
  obtain ⟨u₀, hu₀, hn₀⟩ := exists_mem_dom_normalized
  refine lt_of_lt_of_le hcpos
    (le_csInf ⟨Qform (Real.sqrt 3) u₀, u₀, hu₀, hn₀, rfl⟩ ?_)
  rintro r ⟨u, hu, hn, rfl⟩
  exact hlb u hu hn

/-! ### The `ς² = 1` rigidity: `B(u) > 0` on the unit sphere -/

/-- **Rigidity.**  For every normalized domain element, the `−`-lattice
energy `B(u) = ⟨N₃⁻ςu, ςu⟩ = ∑ σ₃⁻·|ςu|²` is *strictly* positive.

If it vanished, then (since `σ₃⁻ ≥ 3` off its single zero at `ℓ = −2`, i.e.
`m = −1`) `ςu` would be supported at `m = −1` alone; inverting `S` (the
`ℓ²`-isometry `S̃S = 1`) forces `u_a = c·ς̂(−1−a)`, the coefficient
sequence of `ς·e^{-2iθ}`, which is *not* in `H^{1/2}`
(`not_summable_abs_mul_chat_sq`) — contradicting `u ∈ MemDom` once `c ≠ 0`,
and `c = ςu(−1) ≠ 0` because `‖u‖ = 1`.  This is the coefficient content of
the paper's obstruction `ς(θ)e^{-2iθ} ∉ H^{1/2}(S¹)`. -/
lemma B_pos {u : ℤ → ℂ} (hu : MemDom u) (hn : normSq u = 1) :
    0 < ∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2 := by
  have hBsum : Summable (fun m : ℤ => sigM m * ‖convS u m‖ ^ 2) :=
    summable_sigM_mul hu.2
  have hBnn : ∀ m : ℤ, 0 ≤ sigM m * ‖convS u m‖ ^ 2 :=
    fun m => mul_nonneg (sigM_nonneg m) (sq_nonneg _)
  rcases (tsum_nonneg hBnn).lt_or_eq with h | h
  · exact h
  exfalso
  -- `h : 0 = ∑ σ₃⁻|ςu|²`; every term therefore vanishes.
  have hterm : ∀ m : ℤ, sigM m * ‖convS u m‖ ^ 2 = 0 := by
    intro m
    have hle : sigM m * ‖convS u m‖ ^ 2 ≤ ∑' k : ℤ, sigM k * ‖convS u k‖ ^ 2 :=
      hBsum.le_tsum m (fun j _ => hBnn j)
    linarith [hBnn m, h]
  -- Off `m = −1` (where `σ₃⁻ ≥ 3 > 0`), `ςu` vanishes.
  have hconvz : ∀ m : ℤ, m ≠ -1 → convS u m = 0 := by
    intro m hm
    have h3 : (3 : ℝ) ≤ sigM m := sigM_ge_three_of_ne hm
    have hnz : ‖convS u m‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp (hterm m) with h' | h'
      · linarith
      · exact h'
    exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hnz)
  -- Reflection `ς̂(−1−a) = ς̂(a)`.
  have hrefl : ∀ a : ℤ, chat (-1 - a) = chat a := by
    intro a
    rw [show (-1 - a : ℤ) = -(a + 1) by ring, chat_refl,
      show ((a + 1) - 1 : ℤ) = a by ring]
  -- Invert `S`: `u_a = ς̂(−1−a)·ςu(−1)`.
  have husq : Summable (fun n : ℤ => ‖u n‖ ^ 2) := summable_normSq hu.1
  have hSk : convK Sker u = convS u := rfl
  have huformula : ∀ a : ℤ, u a = (chat (-1 - a) : ℂ) * convS u (-1) := by
    intro a
    have hinv := convK_TS_eq husq a
    rw [hSk] at hinv
    rw [← hinv]
    simp only [convK]
    rw [tsum_eq_single (-1) (fun n hn => by rw [hconvz n hn, mul_zero])]
    simp only [Tker]
  have hnormform : ∀ a : ℤ,
      ‖u a‖ ^ 2 = chat (-1 - a) ^ 2 * ‖convS u (-1)‖ ^ 2 := by
    intro a
    rw [huformula a, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  -- `ςu(−1) ≠ 0`, else `u ≡ 0` contradicts `‖u‖ = 1`.
  have hcne : convS u (-1) ≠ 0 := by
    intro h0
    have huz : ∀ a : ℤ, u a = 0 := fun a => by rw [huformula a, h0, mul_zero]
    have hz : normSq u = 0 := by simp [normSq, huz]
    rw [hz] at hn
    exact one_ne_zero hn.symm
  -- The `H^{1/2}` weight of `u` is a positive multiple of `|6a+1|·ς̂(a)²`.
  have hkey : Summable
      (fun a : ℤ => ‖convS u (-1)‖ ^ 2 * (|6 * (a : ℝ) + 1| * chat a ^ 2)) := by
    refine hu.1.congr (fun a => ?_)
    rw [hnormform a, hrefl a]; ring
  have hc2 : ‖convS u (-1)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hcne)
  have hfinal : Summable (fun a : ℤ => |6 * (a : ℝ) + 1| * chat a ^ 2) := by
    refine (hkey.mul_left (‖convS u (-1)‖ ^ 2)⁻¹).congr (fun a => ?_)
    rw [← mul_assoc, inv_mul_cancel₀ hc2, one_mul]
  exact not_summable_abs_mul_chat_sq hfinal

/-- **Paper's `single_crossing`, monotone half: `γ` is strictly increasing on
`(0,∞)`.**  For `0 < s < t`, a minimizer `u` at `t` satisfies `Q_t(u) = γ(t)`
and, being a competitor at `s`, `γ(s) ≤ Q_s(u) = γ(t) − (t²−s²)·B(u)`; the
rigidity `B(u) > 0` (`B_pos`) and `t² > s²` give the strict drop. -/
theorem gam_strictMonoOn : StrictMonoOn gam (Set.Ioi (0 : ℝ)) := by
  intro s hs t ht hst
  rw [Set.mem_Ioi] at hs ht
  obtain ⟨u, hudom, hunorm, humin⟩ := exists_minimizer ht
  have hB : 0 < ∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2 := B_pos hudom hunorm
  have hts : s ^ 2 < t ^ 2 := by
    have h0t : (0 : ℝ) < t := lt_trans hs hst
    nlinarith [hst, hs, h0t]
  have hdiff : Qform s u
      = Qform t u - (t ^ 2 - s ^ 2) * (∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2) := by
    simp only [Qform]; ring
  have hdrop : 0 < (t ^ 2 - s ^ 2) * (∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2) :=
    mul_pos (by linarith) hB
  calc gam s ≤ Qform s u := gam_le hudom hunorm
    _ = Qform t u - (t ^ 2 - s ^ 2) * (∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2) := hdiff
    _ = gam t - (t ^ 2 - s ^ 2) * (∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2) := by rw [humin]
    _ < gam t := by linarith

end KsIndex.Threshold
