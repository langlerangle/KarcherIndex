module

/-
The circle form `Q_s` in the paper's "Frequency parity" and "Threshold"
subsections, represented by Fourier-coefficient sequences.

The domain `MemDom` requires weighted square summability of a sequence
`u : ℤ → ℂ` on frequencies `6n + 1` and of its image on frequencies `6m + 4`.
The sign multiplier is represented by `convS`, with kernel
`chat d = (2/π) * (-1)^d / (2d+1)`. The symbols `sigP` and `sigM` are the
restrictions of `(ℓ²-4)/|ℓ|` to these two lattices.

`Qform s u` is the sum of the `sigP` energy and `s²` times the transformed
`sigM` energy. `gam s` is its infimum over `MemDom` with `normSq u = 1`.
This module supplies symbol estimates, positivity when the head coefficient
vanishes, kernel and Basel identities, an explicit normalized domain witness,
and existence of a normalized minimizer for positive `s`. The direct method
uses coefficientwise compactness, uniformly controlled tails, continuity of
each convolution coordinate, and lower semicontinuity of finite sums.
Concavity after reparameterization by `τ = s²` gives continuity of `gam`
on the positive half-line.

Downstream, `Threshold` proves strict monotonicity and `gam (√3) > 0`;
`GammaOne` proves `gam 1 < 0` using the single-arc trial field. `Statements`
packages the index/nullity dictionary and threshold existence. The physical
Fourier identifications and geometric transports are separate layers; the
coefficient definitions here do not replace those identifications.
-/
public import Mathlib

@[expose] public section


noncomputable section

namespace KsIndex.CircleQ

open Real Filter Topology

/-! ### The symbols on the two frequency lattices -/

/-- The Dirichlet-to-Neumann symbol `σ₃(ℓ) = (ℓ²-4)/|ℓ|` on the `+` lattice
`ℓ = 6n+1`. -/
def sigP (n : ℤ) : ℝ := ((6 * (n : ℝ) + 1) ^ 2 - 4) / |6 * (n : ℝ) + 1|

/-- The symbol on the `-` lattice `ℓ = 6m+4`. -/
def sigM (m : ℤ) : ℝ := ((6 * (m : ℝ) + 4) ^ 2 - 4) / |6 * (m : ℝ) + 4|

lemma abs_freqP_ge_one (n : ℤ) : (1 : ℝ) ≤ |6 * (n : ℝ) + 1| := by
  have h : (1 : ℤ) ≤ |6 * n + 1| := Int.one_le_abs (by omega)
  calc (1 : ℝ) ≤ ((|6 * n + 1| : ℤ) : ℝ) := by exact_mod_cast h
    _ = |6 * (n : ℝ) + 1| := by push_cast; norm_num

lemma abs_freqP_ge_five {n : ℤ} (hn : n ≠ 0) : (5 : ℝ) ≤ |6 * (n : ℝ) + 1| := by
  have h : (5 : ℤ) ≤ |6 * n + 1| := by
    rcases lt_or_gt_of_ne hn with h | h
    · rw [abs_of_neg (by omega : 6 * n + 1 < 0)]; omega
    · rw [abs_of_pos (by omega : 0 < 6 * n + 1)]; omega
  calc (5 : ℝ) ≤ ((|6 * n + 1| : ℤ) : ℝ) := by exact_mod_cast h
    _ = |6 * (n : ℝ) + 1| := by push_cast; norm_num

lemma abs_freqM_ge_two (m : ℤ) : (2 : ℝ) ≤ |6 * (m : ℝ) + 4| := by
  have h : (2 : ℤ) ≤ |6 * m + 4| := by
    rcases le_or_gt 0 m with h | h
    · rw [abs_of_pos (by omega : 0 < 6 * m + 4)]; omega
    · rw [abs_of_neg (by omega : 6 * m + 4 < 0)]; omega
  calc (2 : ℝ) ≤ ((|6 * m + 4| : ℤ) : ℝ) := by exact_mod_cast h
    _ = |6 * (m : ℝ) + 4| := by push_cast; norm_num

lemma abs_freqM_ge_four {m : ℤ} (hm : m ≠ -1) : (4 : ℝ) ≤ |6 * (m : ℝ) + 4| := by
  have h : (4 : ℤ) ≤ |6 * m + 4| := by
    rcases lt_or_gt_of_ne hm with h | h
    · rw [abs_of_neg (by omega : 6 * m + 4 < 0)]; omega
    · rw [abs_of_pos (by omega : 0 < 6 * m + 4)]; omega
  calc (4 : ℝ) ≤ ((|6 * m + 4| : ℤ) : ℝ) := by exact_mod_cast h
    _ = |6 * (m : ℝ) + 4| := by push_cast; norm_num

/-- `σ₃ ≥ -3` on the `+` lattice, with equality exactly at the head `ℓ = 1`. -/
lemma sigP_ge_neg_three (n : ℤ) : -3 ≤ sigP n := by
  have ht := abs_freqP_ge_one n
  have ht0 : (0 : ℝ) < |6 * (n : ℝ) + 1| := by linarith
  rw [sigP, le_div_iff₀ ht0, ← sq_abs (6 * (n : ℝ) + 1)]
  nlinarith

/-- Off the head frequency, `σ₃ ≥ σ₃(-5) = 21/5` on the `+` lattice
(paper display below `qop_ind_plus_nul_above`). -/
lemma sigP_ge_of_ne_zero {n : ℤ} (hn : n ≠ 0) : 21/5 ≤ sigP n := by
  have ht := abs_freqP_ge_five hn
  have ht0 : (0 : ℝ) < |6 * (n : ℝ) + 1| := by linarith
  rw [sigP, div_le_div_iff₀ (by norm_num) ht0, ← sq_abs (6 * (n : ℝ) + 1)] at *
  nlinarith

/-- `σ₃ ≥ 0` on the `-` lattice. -/
lemma sigM_nonneg (m : ℤ) : 0 ≤ sigM m := by
  have ht := abs_freqM_ge_two m
  have ht0 : (0 : ℝ) < |6 * (m : ℝ) + 4| := by linarith
  rw [sigM, le_div_iff₀ ht0, ← sq_abs (6 * (m : ℝ) + 4)]
  nlinarith

/-- The sole zero of `σ₃` on the `-` lattice is `ℓ = -2` (i.e. `m = -1`). -/
lemma sigM_neg_one : sigM (-1) = 0 := by
  norm_num [sigM]

lemma sigM_ge_three_of_ne {m : ℤ} (hm : m ≠ -1) : 3 ≤ sigM m := by
  have ht := abs_freqM_ge_four hm
  have ht0 : (0 : ℝ) < |6 * (m : ℝ) + 4| := by linarith
  rw [sigM, le_div_iff₀ ht0, ← sq_abs (6 * (m : ℝ) + 4)]
  nlinarith

/-- Crude two-sided bound used for summability bookkeeping. -/
lemma abs_sigP_le (n : ℤ) : |sigP n| ≤ 3 * |6 * (n : ℝ) + 1| := by
  have ht := abs_freqP_ge_one n
  have ht0 : (0 : ℝ) < |6 * (n : ℝ) + 1| := by linarith
  rw [sigP, abs_div, abs_abs, div_le_iff₀ ht0]
  rw [abs_le]
  constructor <;> nlinarith [sq_abs (6 * (n : ℝ) + 1), sq_nonneg (6 * (n : ℝ) + 1)]

lemma abs_sigM_le (m : ℤ) : |sigM m| ≤ |6 * (m : ℝ) + 4| := by
  have ht := abs_freqM_ge_two m
  have ht0 : (0 : ℝ) < |6 * (m : ℝ) + 4| := by linarith
  rw [sigM, abs_div, abs_abs, div_le_iff₀ ht0]
  rw [abs_le]
  constructor <;> nlinarith [sq_abs (6 * (m : ℝ) + 4), sq_nonneg (6 * (m : ℝ) + 4)]

/-! ### The sign-pattern kernel -/

/-- The convolution kernel: `chat d = ς̂(6d+3) = (2/π)·(-1)^d/(2d+1)`.
The paper's piecewise formula `6(-1)^{(|ℓ|-3)/6}/(π|ℓ|)` on `ℓ ∈ 3+6ℤ`
collapses to this single expression valid for every `d ∈ ℤ`. -/
def chat (d : ℤ) : ℝ := 2 / π * (-1) ^ d / (2 * (d : ℝ) + 1)

lemma two_mul_add_one_ne_zero (d : ℤ) : 2 * (d : ℝ) + 1 ≠ 0 := by
  have h : (2 * d + 1 : ℤ) ≠ 0 := by omega
  have : ((2 * d + 1 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h
  push_cast at this
  convert this using 2

lemma chat_sq (d : ℤ) : chat d ^ 2 = 4 / π ^ 2 / (2 * (d : ℝ) + 1) ^ 2 := by
  have hpi : π ≠ 0 := pi_ne_zero
  have hd := two_mul_add_one_ne_zero d
  have hz : ((-1 : ℝ) ^ d) ^ 2 = 1 := by
    rcases Int.even_or_odd d with h | h
    · rw [h.neg_one_zpow]; norm_num
    · rw [Odd.neg_one_zpow h]; norm_num
  rw [chat, div_pow, mul_pow, hz, mul_one, div_pow]
  norm_num

/-- Sequence-level form of the paper's key obstruction
`ς(θ)e^{-2iθ} ∉ H^{1/2}(S¹)` (used in the proof of `single_crossing`):
the would-be coefficient sequence of `ς·e^{-2iθ}` on the `+` lattice is
`chat`, and it fails the `H^{1/2}` weight condition. -/
theorem not_summable_abs_mul_chat_sq :
    ¬ Summable (fun n : ℤ => |6 * (n : ℝ) + 1| * chat n ^ 2) := by
  intro hs
  have hπ : (0 : ℝ) < π := pi_pos
  -- Restrict to ℕ ⊂ ℤ.
  have h1 : Summable (fun n : ℕ => |6 * ((n : ℤ) : ℝ) + 1| * chat (n : ℤ) ^ 2) :=
    hs.comp_injective Nat.cast_injective
  -- Compare with the harmonic series.
  have h2 : Summable (fun n : ℕ => 4 / π ^ 2 * (1 / ((n : ℝ) + 1))) := by
    refine h1.of_nonneg_of_le (fun n => by positivity) fun n => ?_
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [chat_sq]
    push_cast
    rw [abs_of_pos (by linarith : (0 : ℝ) < 6 * (n : ℝ) + 1),
        show (6 * (n : ℝ) + 1) * (4 / π ^ 2 / (2 * (n : ℝ) + 1) ^ 2)
          = 4 / π ^ 2 * ((6 * (n : ℝ) + 1) / (2 * (n : ℝ) + 1) ^ 2) by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (n : ℝ)]
  have h3 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    have h := h2.mul_left (π ^ 2 / 4)
    have hfun : (fun n : ℕ => π ^ 2 / 4 * (4 / π ^ 2 * (1 / ((n : ℝ) + 1))))
        = fun n : ℕ => 1 / ((n : ℝ) + 1) := by
      funext n
      have hpi : π ≠ 0 := pi_ne_zero
      field_simp
    rwa [hfun] at h
  have h4 : Summable (fun n : ℕ => 1 / ((n : ℝ))) := by
    have hfun : (fun n : ℕ => 1 / ((n : ℝ) + 1))
        = fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) := by
      funext n; push_cast; rfl
    rw [hfun] at h3
    exact (summable_nat_add_iff 1).mp h3
  exact not_summable_one_div_natCast h4

/-! ### The sequence spaces and the form `Q_s` -/

/-- The convolution realizing the sign multiplier `u ↦ ς·u` from the `+`
lattice to the `-` lattice: `(Su)(6m+4) = Σ_n ς̂((6m+4)-(6n+1))·û(6n+1)`. -/
def convS (u : ℤ → ℂ) (m : ℤ) : ℂ := ∑' n : ℤ, (chat (m - n) : ℂ) * u n

/-- Membership in (the coefficient model of) `H^{1/2}_{ς,(+,2;3)}(S¹)`:
both `u` and `ς·u` satisfy the `H^{1/2}` weight condition.  Since `|ℓ| ≥ 1`
on both lattices, plain square-summability is implied. -/
def MemDom (u : ℤ → ℂ) : Prop :=
  Summable (fun n : ℤ => |6 * (n : ℝ) + 1| * ‖u n‖ ^ 2)
    ∧ Summable (fun m : ℤ => |6 * (m : ℝ) + 4| * ‖convS u m‖ ^ 2)

/-- Squared `L²` norm (of the coefficient sequence). -/
def normSq (u : ℤ → ℂ) : ℝ := ∑' n : ℤ, ‖u n‖ ^ 2

/-- The quadratic form `Q_s(u,u)` of the paper ("Frequency parity"):
`⟨N₃⁺u, u⟩ + s²⟨N₃⁻ςu, ςu⟩` in coefficients. -/
def Qform (s : ℝ) (u : ℤ → ℂ) : ℝ :=
  (∑' n : ℤ, sigP n * ‖u n‖ ^ 2) + s ^ 2 * ∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2

/-- The least-eigenvalue function `γ(s)` ("Threshold"). -/
def gam (s : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ u : ℤ → ℂ, MemDom u ∧ normSq u = 1 ∧ Qform s u = r}

/-! ### Summability bookkeeping -/

lemma summable_normSq {u : ℤ → ℂ}
    (hu : Summable (fun n : ℤ => |6 * (n : ℝ) + 1| * ‖u n‖ ^ 2)) :
    Summable (fun n : ℤ => ‖u n‖ ^ 2) :=
  hu.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun n => le_mul_of_one_le_left (sq_nonneg _) (abs_freqP_ge_one n))

lemma summable_sigP_mul {u : ℤ → ℂ}
    (hu : Summable (fun n : ℤ => |6 * (n : ℝ) + 1| * ‖u n‖ ^ 2)) :
    Summable (fun n : ℤ => sigP n * ‖u n‖ ^ 2) := by
  have habs : Summable (fun n : ℤ => |sigP n * ‖u n‖ ^ 2|) := by
    refine (hu.mul_left 3).of_nonneg_of_le (fun n => abs_nonneg _) fun n => ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖u n‖)]
    calc |sigP n| * ‖u n‖ ^ 2
        ≤ 3 * |6 * (n : ℝ) + 1| * ‖u n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (abs_sigP_le n) (sq_nonneg _)
      _ = 3 * (|6 * (n : ℝ) + 1| * ‖u n‖ ^ 2) := by ring
  exact habs.of_abs

lemma summable_sigM_mul {u : ℤ → ℂ}
    (hu : Summable (fun m : ℤ => |6 * (m : ℝ) + 4| * ‖convS u m‖ ^ 2)) :
    Summable (fun m : ℤ => sigM m * ‖convS u m‖ ^ 2) := by
  have habs : Summable (fun m : ℤ => |sigM m * ‖convS u m‖ ^ 2|) := by
    refine hu.of_nonneg_of_le (fun m => abs_nonneg _) fun m => ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖convS u m‖)]
    exact mul_le_mul_of_nonneg_right (abs_sigM_le m) (sq_nonneg _)
  exact habs.of_abs

/-! ### The `ind + nul ≤ 1` mechanism -/

/-- Core of the paper's `qop_ind_plus_nul_above` (`ind(Q_s) + nul(Q_s) ≤ 1`):
any nonzero domain element with vanishing head coefficient (`ℓ = 1`) has
strictly positive `Q_s`-energy, for EVERY `s`.  Consequently no
two-dimensional subspace can be `Q_s`-nonpositive. -/
theorem Qform_pos_of_head_zero {s : ℝ} {u : ℤ → ℂ} (hu : MemDom u)
    (h0 : u 0 = 0) (hne : ∃ n, u n ≠ 0) : 0 < Qform s u := by
  obtain ⟨hu1, hu2⟩ := hu
  have hl2 : Summable (fun n : ℤ => ‖u n‖ ^ 2) := summable_normSq hu1
  have hsig := summable_sigP_mul hu1
  have hpt : ∀ n : ℤ, 21/5 * ‖u n‖ ^ 2 ≤ sigP n * ‖u n‖ ^ 2 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [h0]
    · exact mul_le_mul_of_nonneg_right (sigP_ge_of_ne_zero hn) (sq_nonneg _)
  obtain ⟨n₀, hn₀⟩ := hne
  have hn₀' : 0 < ‖u n₀‖ ^ 2 := by positivity
  have hposl2 : 0 < ∑' n : ℤ, ‖u n‖ ^ 2 :=
    hl2.tsum_pos (fun n => sq_nonneg _) n₀ hn₀'
  have h1 : 21/5 * ∑' n : ℤ, ‖u n‖ ^ 2 ≤ ∑' n : ℤ, sigP n * ‖u n‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact (hl2.mul_left _).tsum_le_tsum hpt hsig
  have h2 : (0 : ℝ) ≤ ∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2 :=
    tsum_nonneg fun m => mul_nonneg (sigM_nonneg m) (sq_nonneg _)
  have h3 : (0 : ℝ) ≤ s ^ 2 * ∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2 :=
    mul_nonneg (sq_nonneg s) h2
  rw [Qform]
  nlinarith

/-! ### The Basel ladder: the paper's Parseval identity -/

/-- Odd Basel sum over `ℕ`: `Σ_{n≥0} 1/(2n+1)² = π²/8`. -/
theorem hasSum_nat_odd_sq_inv :
    HasSum (fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 2) (π ^ 2 / 8) := by
  have htot := hasSum_zeta_two
  -- Even part: `Σ 1/(2k)² = π²/24`.
  have heven : HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 2) (π ^ 2 / 24) := by
    have h := hasSum_zeta_two.mul_left (1/4)
    have hfun : (fun k : ℕ => 1/4 * ((1 : ℝ) / (k : ℝ) ^ 2))
        = fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 2 := by
      funext k
      push_cast
      rcases eq_or_ne (k : ℝ) 0 with h0 | h0
      · rw [h0]; norm_num
      · field_simp
        ring
    rw [hfun] at h
    rw [show π ^ 2 / 24 = 1/4 * (π ^ 2 / 6) by ring]
    exact h
  -- Odd part is summable (injective reindexing of the full series).
  have hoddS : Summable (fun n : ℕ => (1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
    have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
      intro a b hab
      have hab' : 2 * a + 1 = 2 * b + 1 := hab
      omega
    exact htot.summable.comp_injective hinj
  have hcomb : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)
      (π ^ 2 / 24 + ∑' n : ℕ, (1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ) ^ 2) :=
    HasSum.even_add_odd (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) heven hoddS.hasSum
  have hval : π ^ 2 / 24 + (∑' n : ℕ, (1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ) ^ 2) = π ^ 2 / 6 :=
    hcomb.unique htot
  have hodd : HasSum (fun n : ℕ => (1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ) ^ 2) (π ^ 2 / 8) := by
    have h := hoddS.hasSum
    rw [show (∑' n : ℕ, (1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ) ^ 2) = π ^ 2 / 8 by linarith] at h
    exact h
  have hfun : (fun n : ℕ => (1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ) ^ 2)
      = fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 2 := by
    funext n
    push_cast
    norm_num
  rwa [hfun] at hodd

/-- Odd Basel sum over `ℤ`: `Σ_{d∈ℤ} 1/(2d+1)² = π²/4`. -/
theorem hasSum_int_odd_sq_inv :
    HasSum (fun d : ℤ => (1 : ℝ) / (2 * (d : ℝ) + 1) ^ 2) (π ^ 2 / 4) := by
  have h₁ : HasSum (fun n : ℕ => (1 : ℝ) / (2 * (((n : ℤ)) : ℝ) + 1) ^ 2) (π ^ 2 / 8) := by
    have hfun : (fun n : ℕ => (1 : ℝ) / (2 * (((n : ℤ)) : ℝ) + 1) ^ 2)
        = fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 2 := by
      funext n; push_cast; norm_num
    rw [hfun]
    exact hasSum_nat_odd_sq_inv
  have h₂ : HasSum (fun n : ℕ => (1 : ℝ) / (2 * (((-((n : ℤ) + 1)) : ℤ) : ℝ) + 1) ^ 2)
      (π ^ 2 / 8) := by
    have hfun : (fun n : ℕ => (1 : ℝ) / (2 * (((-((n : ℤ) + 1)) : ℤ) : ℝ) + 1) ^ 2)
        = fun n : ℕ => (1 : ℝ) / (2 * (n : ℝ) + 1) ^ 2 := by
      funext n
      push_cast
      rw [show 2 * (-((n : ℝ) + 1)) + 1 = -(2 * (n : ℝ) + 1) by ring, neg_sq]
    rw [hfun]
    exact hasSum_nat_odd_sq_inv
  have h := HasSum.of_nat_of_neg_add_one
    (f := fun d : ℤ => (1 : ℝ) / (2 * (d : ℝ) + 1) ^ 2) h₁ h₂
  rw [show π ^ 2 / 4 = π ^ 2 / 8 + π ^ 2 / 8 by ring]
  exact h

/-- The paper's Parseval identity for the sign pattern
(`π²/36 = Σ_{ℓ∈1+6ℤ} 1/(ℓ+2)²`, in lattice coordinates `ℓ+2 = 6d+3`):
`Σ_{d∈ℤ} 1/(6d+3)² = π²/36`. -/
theorem hasSum_int_six_shift_sq_inv :
    HasSum (fun d : ℤ => (1 : ℝ) / (6 * (d : ℝ) + 3) ^ 2) (π ^ 2 / 36) := by
  have h := hasSum_int_odd_sq_inv.mul_left (1/9)
  have hfun : (fun d : ℤ => 1/9 * ((1 : ℝ) / (2 * (d : ℝ) + 1) ^ 2))
      = fun d : ℤ => (1 : ℝ) / (6 * (d : ℝ) + 3) ^ 2 := by
    funext d
    have hd := two_mul_add_one_ne_zero d
    rw [show 6 * (d : ℝ) + 3 = 3 * (2 * (d : ℝ) + 1) by ring]
    field_simp
    ring
  rw [hfun] at h
  rw [show π ^ 2 / 36 = 1/9 * (π ^ 2 / 4) by ring]
  exact h

/-! ### The threshold computation's rational leaf -/

/-- The eight-term finite sum from the proof of `threshold_upper_bound`
(`γ(√3) > 0`): the partial sum of `(π²/36)(1-S)` over `n ∈ [-4,3]`. -/
theorem threshold_finite_sum :
    (25 : ℚ)/15372 + 19/6570 + 13/1944 + 7/198 - 1/18 + 5/972 + 11/4230 + 17/11088
      = 88090307/313283512080 := by
  norm_num

/-! ### An explicit domain element -/

lemma neg_one_zpow_sq (d : ℤ) : ((-1 : ℝ) ^ d) ^ 2 = 1 := by
  rcases Int.even_or_odd d with h | h
  · rw [h.neg_one_zpow]; norm_num
  · rw [Odd.neg_one_zpow h]; norm_num

lemma two_mul_sub_one_ne_zero (m : ℤ) : 2 * (m : ℝ) - 1 ≠ 0 := by
  have h := two_mul_add_one_ne_zero (m - 1)
  push_cast at h
  intro hcon
  apply h
  linarith

lemma sq_pos_of_ne_zero' {x : ℝ} (hx : x ≠ 0) : 0 < x ^ 2 :=
  lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 hx))

/-- Adjacent kernel values telescope:
`chat m + chat (m-1) = -(4/π)·(-1)^m/((2m+1)(2m-1))` — decay `1/m²`, one
order better than `chat` itself.  This head-cancellation mechanism is what
admits explicit two-point domain elements. -/
lemma chat_add_prev (m : ℤ) :
    chat m + chat (m - 1)
      = -4 / π * (-1) ^ m / ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) - 1)) := by
  have h1 : ((-1 : ℝ)) ^ (m - 1) = -(-1 : ℝ) ^ m := by
    rw [zpow_sub_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
    norm_num
  have hm1 : 2 * (m : ℝ) + 1 ≠ 0 := two_mul_add_one_ne_zero m
  have hm2 : 2 * (m : ℝ) - 1 ≠ 0 := two_mul_sub_one_ne_zero m
  have hpi : π ≠ 0 := pi_ne_zero
  simp only [chat]
  rw [h1]
  push_cast
  rw [show 2 * ((m : ℝ) - 1) + 1 = 2 * (m : ℝ) - 1 by ring]
  field_simp
  ring

/-- The two-point domain witness `(δ₀ + δ₁)/√2` (frequencies `ℓ = 1, 7`):
the head cancellation `(-1)⁰·1 + (-1)¹·1 = 0` upgrades the convolution decay
from `1/m` to `1/m²`, sufficient for the weighted square summability
required by `H^{1/2}`-membership of `ς·u`. -/
def wit : ℤ → ℂ := fun n => if n = 0 ∨ n = 1 then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0

lemma wit_apply_zero : wit 0 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by simp [wit]

lemma wit_apply_one : wit 1 = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by simp [wit]

lemma wit_apply_ne {b : ℤ} (h0 : b ≠ 0) (h1 : b ≠ 1) : wit b = 0 := by
  simp [wit, h0, h1]

lemma normSq_wit : normSq wit = 1 := by
  have hvanish : ∀ b ∉ ({0, 1} : Finset ℤ), ‖wit b‖ ^ 2 = 0 := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    rw [wit_apply_ne hb.1 hb.2]
    norm_num
  rw [normSq, tsum_eq_sum hvanish, Finset.sum_insert (by norm_num),
      Finset.sum_singleton, wit_apply_zero, wit_apply_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹),
      inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma convS_wit (m : ℤ) :
    convS wit m = (((chat m + chat (m - 1)) * (Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  have hvanish : ∀ b ∉ ({0, 1} : Finset ℤ), (chat (m - b) : ℂ) * wit b = 0 := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    rw [wit_apply_ne hb.1 hb.2, mul_zero]
  rw [convS, tsum_eq_sum hvanish, Finset.sum_insert (by norm_num),
      Finset.sum_singleton, wit_apply_zero, wit_apply_one, sub_zero]
  push_cast
  ring

lemma norm_convS_wit_sq (m : ℤ) :
    ‖convS wit m‖ ^ 2 = (chat m + chat (m - 1)) ^ 2 / 2 := by
  rw [convS_wit, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- Cleared-denominator bound for the telescoped kernel pair. -/
lemma chat_pair_sq_bound (m : ℤ) :
    (chat m + chat (m - 1)) ^ 2 * ((2 * (m : ℝ) + 1) ^ 2 * (2 * (m : ℝ) - 1) ^ 2)
      ≤ 4 := by
  have hm1 := two_mul_add_one_ne_zero m
  have hm2 := two_mul_sub_one_ne_zero m
  rw [chat_add_prev, div_pow, mul_pow, neg_one_zpow_sq, mul_one,
      mul_pow (2 * (m : ℝ) + 1) (2 * (m : ℝ) - 1),
      div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero 2 hm1) (pow_ne_zero 2 hm2)),
      show ((-4 : ℝ) / π) ^ 2 = 16 / π ^ 2 by rw [div_pow]; norm_num,
      div_le_iff₀ (by positivity)]
  nlinarith [pi_gt_three, sq_nonneg (π - 3)]

lemma abs_freqM_le (m : ℤ) : |6 * (m : ℝ) + 4| ≤ 4 * (2 * (m : ℝ) + 1) ^ 2 := by
  rcases le_or_gt 0 m with h | h
  · have h' : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]
    nlinarith
  · have h'' : m ≤ -1 := by omega
    have h' : (m : ℝ) ≤ -1 := by exact_mod_cast h''
    rw [abs_of_neg (by linarith : 6 * (m : ℝ) + 4 < 0)]
    nlinarith [sq_nonneg (16 * (m : ℝ) + 11)]

lemma summable_majorant : Summable (fun m : ℤ => 8 / (2 * (m : ℝ) - 1) ^ 2) := by
  have hinj : Function.Injective (fun m : ℤ => m - 1) := by
    intro a b hab
    have hab' : a - 1 = b - 1 := hab
    omega
  have h := (hasSum_int_odd_sq_inv.summable.mul_left 8).comp_injective hinj
  have hfun : ((fun d : ℤ => 8 * ((1 : ℝ) / (2 * (d : ℝ) + 1) ^ 2)) ∘ fun m : ℤ => m - 1)
      = fun m : ℤ => 8 / (2 * (m : ℝ) - 1) ^ 2 := by
    funext m
    simp only [Function.comp_apply]
    push_cast
    rw [show 2 * ((m : ℝ) - 1) + 1 = 2 * (m : ℝ) - 1 by ring]
    ring
  rwa [hfun] at h

lemma summable_weight_wit :
    Summable (fun n : ℤ => |6 * (n : ℝ) + 1| * ‖wit n‖ ^ 2) := by
  apply summable_of_ne_finset_zero (s := ({0, 1} : Finset ℤ))
  intro b hb
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  rw [wit_apply_ne hb.1 hb.2]
  norm_num

lemma summable_weight_convS_wit :
    Summable (fun m : ℤ => |6 * (m : ℝ) + 4| * ‖convS wit m‖ ^ 2) := by
  refine summable_majorant.of_nonneg_of_le (fun m => by positivity) fun m => ?_
  have hm2 : (0 : ℝ) < (2 * (m : ℝ) - 1) ^ 2 :=
    sq_pos_of_ne_zero' (two_mul_sub_one_ne_zero m)
  rw [norm_convS_wit_sq, le_div_iff₀ hm2]
  have h1 := chat_pair_sq_bound m
  have h2 := abs_freqM_le m
  have h3 : (0 : ℝ) ≤ (chat m + chat (m - 1)) ^ 2 * (2 * (m : ℝ) - 1) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right h2 h3]

lemma memDom_wit : MemDom wit := ⟨summable_weight_wit, summable_weight_convS_wit⟩

/-- Domain nonemptiness, by the explicit two-point witness. -/
theorem exists_mem_dom_normalized : ∃ u : ℤ → ℂ, MemDom u ∧ normSq u = 1 :=
  ⟨wit, memDom_wit, normSq_wit⟩

/-! ### Concavity in `τ = s²` and continuity of `γ` -/

/-- The energy at parameter `τ = s²`. -/
def Qtau (τ : ℝ) (u : ℤ → ℂ) : ℝ :=
  (∑' n : ℤ, sigP n * ‖u n‖ ^ 2) + τ * ∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2

lemma Qform_eq_Qtau (s : ℝ) (u : ℤ → ℂ) : Qform s u = Qtau (s ^ 2) u := rfl

/-- `γ` reparameterized by `τ = s²`. -/
def gamTau (τ : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ u : ℤ → ℂ, MemDom u ∧ normSq u = 1 ∧ Qtau τ u = r}

lemma gam_eq_gamTau (s : ℝ) : gam s = gamTau (s ^ 2) := rfl

lemma Qtau_ge_neg_three {τ : ℝ} (hτ : 0 ≤ τ) {u : ℤ → ℂ} (hu : MemDom u)
    (hn : normSq u = 1) : -3 ≤ Qtau τ u := by
  have hl2 : Summable (fun n : ℤ => ‖u n‖ ^ 2) := summable_normSq hu.1
  have hsig := summable_sigP_mul hu.1
  have hpt : ∀ n : ℤ, -3 * ‖u n‖ ^ 2 ≤ sigP n * ‖u n‖ ^ 2 :=
    fun n => mul_le_mul_of_nonneg_right (sigP_ge_neg_three n) (sq_nonneg _)
  have h1 : -3 * ∑' n : ℤ, ‖u n‖ ^ 2 ≤ ∑' n : ℤ, sigP n * ‖u n‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact (hl2.mul_left _).tsum_le_tsum hpt hsig
  have h2 : (0 : ℝ) ≤ τ * ∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2 :=
    mul_nonneg hτ (tsum_nonneg fun m => mul_nonneg (sigM_nonneg m) (sq_nonneg _))
  rw [normSq] at hn
  rw [hn] at h1
  rw [Qtau]
  linarith

lemma gamTau_bddBelow {τ : ℝ} (hτ : 0 ≤ τ) :
    BddBelow {r : ℝ | ∃ u : ℤ → ℂ, MemDom u ∧ normSq u = 1 ∧ Qtau τ u = r} := by
  refine ⟨-3, ?_⟩
  rintro r ⟨u, hu, hn, rfl⟩
  exact Qtau_ge_neg_three hτ hu hn

lemma gamTau_set_nonempty (τ : ℝ) :
    {r : ℝ | ∃ u : ℤ → ℂ, MemDom u ∧ normSq u = 1 ∧ Qtau τ u = r}.Nonempty :=
  ⟨Qtau τ wit, wit, memDom_wit, normSq_wit, rfl⟩

lemma gamTau_le {τ : ℝ} (hτ : 0 ≤ τ) {u : ℤ → ℂ} (hu : MemDom u)
    (hn : normSq u = 1) : gamTau τ ≤ Qtau τ u :=
  csInf_le (gamTau_bddBelow hτ) ⟨u, hu, hn, rfl⟩

/-- `γ`, as a function of `τ = s²`, is an infimum of affine functions of `τ`,
hence concave on `[0,∞)` — the paper's continuity mechanism in
`single_crossing`. -/
lemma gamTau_concaveOn : ConcaveOn ℝ (Set.Ici (0 : ℝ)) gamTau := by
  refine ⟨convex_Ici 0, ?_⟩
  intro τ₁ h₁ τ₂ h₂ a b ha hb hab
  simp only [smul_eq_mul]
  rw [Set.mem_Ici] at h₁ h₂
  refine le_csInf (gamTau_set_nonempty _) ?_
  rintro r ⟨u, hu, hn, rfl⟩
  have e : Qtau (a * τ₁ + b * τ₂) u = a * Qtau τ₁ u + b * Qtau τ₂ u := by
    simp only [Qtau]
    linear_combination (-(∑' n : ℤ, sigP n * ‖u n‖ ^ 2)) * hab
  rw [e]
  exact add_le_add (mul_le_mul_of_nonneg_left (gamTau_le h₁ hu hn) ha)
    (mul_le_mul_of_nonneg_left (gamTau_le h₂ hu hn) hb)

/-! ### Direct-method infrastructure for `exists_minimizer` -/

/-- `ℓ²` summability of the shifted kernel. -/
lemma summable_chat_shift_sq (m : ℤ) : Summable (fun n : ℤ => chat (m - n) ^ 2) := by
  have hinj : Function.Injective (fun n : ℤ => m - n) := by
    intro a b hab
    have hab' : m - a = m - b := hab
    omega
  have h := (hasSum_int_odd_sq_inv.summable.mul_left (4 / π ^ 2)).comp_injective hinj
  have hfun : ((fun d : ℤ => 4 / π ^ 2 * ((1 : ℝ) / (2 * (d : ℝ) + 1) ^ 2)) ∘
      fun n : ℤ => m - n) = fun n : ℤ => chat (m - n) ^ 2 := by
    funext n
    simp only [Function.comp_apply]
    rw [chat_sq]
    push_cast
    ring
  rwa [hfun] at h

/-- Absolute summability of the convolution integrand for an `ℓ²` sequence
(AM–GM comparison `|k|·‖w‖ ≤ k² + ‖w‖²`). -/
lemma summable_norm_conv_term {w : ℤ → ℂ} (hw : Summable fun n : ℤ => ‖w n‖ ^ 2)
    (m : ℤ) : Summable (fun n : ℤ => ‖(chat (m - n) : ℂ) * w n‖) := by
  refine ((summable_chat_shift_sq m).add hw).of_nonneg_of_le
    (fun n => norm_nonneg _) fun n => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  nlinarith [sq_nonneg (|chat (m - n)| - ‖w n‖), sq_abs (chat (m - n)),
    mul_nonneg (abs_nonneg (chat (m - n))) (norm_nonneg (w n))]

lemma summable_conv_term {w : ℤ → ℂ} (hw : Summable fun n : ℤ => ‖w n‖ ^ 2)
    (m : ℤ) : Summable (fun n : ℤ => (chat (m - n) : ℂ) * w n) :=
  (summable_norm_conv_term hw m).of_norm

/-- Coercivity of the `+`-symbol: the `H^{1/2}` weight is dominated by `σ₃+4`. -/
lemma weight_le_sigP_add_four (n : ℤ) : |6 * (n : ℝ) + 1| ≤ sigP n + 4 := by
  have ht := abs_freqP_ge_one n
  have ht0 : (0 : ℝ) < |6 * (n : ℝ) + 1| := by linarith
  rw [sigP, ← sq_abs (6 * (n : ℝ) + 1), div_add' _ _ _ (ne_of_gt ht0),
    le_div_iff₀ ht0]
  nlinarith

lemma weight_le_sigM_add_two (m : ℤ) : |6 * (m : ℝ) + 4| ≤ sigM m + 2 := by
  have ht := abs_freqM_ge_two m
  have ht0 : (0 : ℝ) < |6 * (m : ℝ) + 4| := by linarith
  rw [sigM, ← sq_abs (6 * (m : ℝ) + 4), div_add' _ _ _ (ne_of_gt ht0),
    le_div_iff₀ ht0]
  nlinarith

/-- tsum-level coercivity: the `H^{1/2}` weight sum is controlled by the `σ₊`
energy plus the `L²` mass. -/
lemma tsum_weight_le {u : ℤ → ℂ} (hu : MemDom u) :
    (∑' n : ℤ, |6 * (n : ℝ) + 1| * ‖u n‖ ^ 2)
      ≤ (∑' n : ℤ, sigP n * ‖u n‖ ^ 2) + 4 * normSq u := by
  have hl2 := summable_normSq hu.1
  have hsum := (summable_sigP_mul hu.1).add (hl2.mul_left 4)
  have h1 : (∑' n : ℤ, |6 * (n : ℝ) + 1| * ‖u n‖ ^ 2)
      ≤ ∑' n : ℤ, (sigP n * ‖u n‖ ^ 2 + 4 * ‖u n‖ ^ 2) := by
    refine hu.1.tsum_le_tsum (fun n => ?_) hsum
    have := weight_le_sigP_add_four n
    nlinarith [sq_nonneg ‖u n‖]
  rw [(summable_sigP_mul hu.1).tsum_add (hl2.mul_left 4), tsum_mul_left] at h1
  exact h1

/-- Tails of a summable real series can be made arbitrarily small. -/
lemma exists_finset_tsum_compl_lt {f : ℤ → ℝ} (hf : Summable f) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ F : Finset ℤ, (∑' n : ((↑F : Set ℤ)ᶜ : Set ℤ), f ↑n) < ε := by
  have hten : Tendsto (fun F : Finset ℤ => ∑ n ∈ F, f n) atTop
      (𝓝 (∑' n : ℤ, f n)) := hf.hasSum
  have h2 : ∀ᶠ F : Finset ℤ in atTop, (∑' n : ℤ, f n) - ε < ∑ n ∈ F, f n :=
    hten.eventually (eventually_gt_nhds (by linarith))
  obtain ⟨F, hF⟩ := h2.exists
  refine ⟨F, ?_⟩
  have hsplit := hf.tsum_subtype_add_tsum_subtype_compl (↑F : Set ℤ)
  rw [Finset.tsum_subtype'] at hsplit
  linarith

/-- Weighted AM–GM for the tail estimate: `|a|·‖z‖ ≤ a²/(2δ) + (δ/2)‖z‖²`. -/
lemma norm_real_mul_le {δ : ℝ} (hδ : 0 < δ) (a : ℝ) (z : ℂ) :
    ‖(a : ℂ) * z‖ ≤ (2 * δ)⁻¹ * a ^ 2 + δ / 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hpoly : |a| * ‖z‖ * (2 * δ) ≤ a ^ 2 + δ ^ 2 * ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg (|a| - δ * ‖z‖), sq_abs a]
  have heq : (2 * δ)⁻¹ * a ^ 2 + δ / 2 * ‖z‖ ^ 2
      = (a ^ 2 + δ ^ 2 * ‖z‖ ^ 2) / (2 * δ) := by
    field_simp
  rw [heq, le_div_iff₀ (by positivity)]
  exact hpoly

/-- The convolution tail over the complement of a kernel-adapted finset is
uniformly small over the `ℓ²` unit ball. -/
lemma norm_tsum_conv_compl_le {w : ℤ → ℂ} (hw : Summable fun n : ℤ => ‖w n‖ ^ 2)
    (hwbd : (∑' n : ℤ, ‖w n‖ ^ 2) ≤ 1) (m : ℤ) (F : Finset ℤ) {δ : ℝ}
    (hδ : 0 < δ)
    (hF : (∑' n : ((↑F : Set ℤ)ᶜ : Set ℤ), chat (m - ↑n) ^ 2) ≤ δ * δ) :
    ‖∑' n : ((↑F : Set ℤ)ᶜ : Set ℤ), (chat (m - ↑n) : ℂ) * w ↑n‖ ≤ δ := by
  have hnormsub : Summable (fun n : ((↑F : Set ℤ)ᶜ : Set ℤ) =>
      ‖(chat (m - ↑n) : ℂ) * w ↑n‖) :=
    (summable_norm_conv_term hw m).subtype _
  have hchat_sub : Summable
      (fun n : ((↑F : Set ℤ)ᶜ : Set ℤ) => chat (m - ↑n) ^ 2) :=
    (summable_chat_shift_sq m).subtype _
  have hw_sub : Summable (fun n : ((↑F : Set ℤ)ᶜ : Set ℤ) => ‖w ↑n‖ ^ 2) :=
    hw.subtype _
  have hmaj : Summable (fun n : ((↑F : Set ℤ)ᶜ : Set ℤ) =>
      (2 * δ)⁻¹ * chat (m - ↑n) ^ 2 + δ / 2 * ‖w ↑n‖ ^ 2) :=
    (hchat_sub.mul_left _).add (hw_sub.mul_left _)
  refine (norm_tsum_le_tsum_norm hnormsub).trans ?_
  refine (hnormsub.tsum_le_tsum (fun n => norm_real_mul_le hδ _ _) hmaj).trans ?_
  have hsum_eq : (∑' n : ((↑F : Set ℤ)ᶜ : Set ℤ),
      ((2 * δ)⁻¹ * chat (m - ↑n) ^ 2 + δ / 2 * ‖w ↑n‖ ^ 2))
      = (2 * δ)⁻¹ * (∑' n : ((↑F : Set ℤ)ᶜ : Set ℤ), chat (m - ↑n) ^ 2)
        + δ / 2 * ∑' n : ((↑F : Set ℤ)ᶜ : Set ℤ), ‖w ↑n‖ ^ 2 := by
    have h := (hchat_sub.mul_left ((2 * δ)⁻¹)).tsum_add (hw_sub.mul_left (δ / 2))
    rw [tsum_mul_left, tsum_mul_left] at h
    exact h
  rw [hsum_eq]
  have h2 : (∑' n : ((↑F : Set ℤ)ᶜ : Set ℤ), ‖w ↑n‖ ^ 2) ≤ 1 :=
    (Summable.tsum_subtype_le _ _ (fun n => sq_nonneg _) hw).trans hwbd
  have hq : (0 : ℝ) < (2 * δ)⁻¹ := by positivity
  have hcalc : (2 * δ)⁻¹ * (δ * δ) + δ / 2 * 1 = δ := by
    field_simp
    ring
  have hb1 := mul_le_mul_of_nonneg_left hF (le_of_lt hq)
  have hb2 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ δ / 2)
  linarith

/-- Coordinatewise continuity of `convS` along pointwise-convergent sequences
in the `ℓ²` unit ball: the kernel tail is `ℓ²`-uniform, the head is a finite
sum.  This is the direct method's replacement for weak continuity. -/
lemma tendsto_convS {v : ℕ → ℤ → ℂ} {u : ℤ → ℂ}
    (hpt : ∀ n : ℤ, Tendsto (fun j => v j n) atTop (𝓝 (u n)))
    (hvsum : ∀ j, Summable fun n : ℤ => ‖v j n‖ ^ 2)
    (hvbd : ∀ j, (∑' n : ℤ, ‖v j n‖ ^ 2) ≤ 1)
    (husum : Summable fun n : ℤ => ‖u n‖ ^ 2)
    (hubd : (∑' n : ℤ, ‖u n‖ ^ 2) ≤ 1) (m : ℤ) :
    Tendsto (fun j => convS (v j) m) atTop (𝓝 (convS u m)) := by
  rw [← tendsto_sub_nhds_zero_iff, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hδ : (0 : ℝ) < ε / 3 := by positivity
  obtain ⟨F, hF⟩ := exists_finset_tsum_compl_lt (summable_chat_shift_sq m)
    (mul_pos hδ hδ)
  have hsplit : ∀ w : ℤ → ℂ, Summable (fun n : ℤ => ‖w n‖ ^ 2) →
      convS w m = (∑ n ∈ F, (chat (m - n) : ℂ) * w n)
        + ∑' n : ((↑F : Set ℤ)ᶜ : Set ℤ), (chat (m - ↑n) : ℂ) * w ↑n := by
    intro w hw
    have h := (summable_conv_term hw m).tsum_subtype_add_tsum_subtype_compl
      (↑F : Set ℤ)
    have hhead_eq : (∑' x : (↑F : Set ℤ), (chat (m - ↑x) : ℂ) * w ↑x)
        = ∑ n ∈ F, (chat (m - n) : ℂ) * w n :=
      Finset.tsum_subtype' F (fun n => (chat (m - n) : ℂ) * w n)
    rw [hhead_eq] at h
    rw [convS, ← h]
  have htails : ∀ w : ℤ → ℂ, Summable (fun n : ℤ => ‖w n‖ ^ 2) →
      (∑' n : ℤ, ‖w n‖ ^ 2) ≤ 1 →
      ‖∑' n : ((↑F : Set ℤ)ᶜ : Set ℤ), (chat (m - ↑n) : ℂ) * w ↑n‖ ≤ ε / 3 :=
    fun w hw hwbd => norm_tsum_conv_compl_le hw hwbd m F hδ (le_of_lt hF)
  have hhead : Tendsto (fun j => ∑ n ∈ F, (chat (m - n) : ℂ) * v j n) atTop
      (𝓝 (∑ n ∈ F, (chat (m - n) : ℂ) * u n)) :=
    tendsto_finsetSum _ fun n _ => (hpt n).const_mul _
  have hheadev : ∀ᶠ j in atTop,
      ‖(∑ n ∈ F, (chat (m - n) : ℂ) * v j n)
        - ∑ n ∈ F, (chat (m - n) : ℂ) * u n‖ < ε / 3 := by
    have h0 : Tendsto (fun j => (∑ n ∈ F, (chat (m - n) : ℂ) * v j n)
        - ∑ n ∈ F, (chat (m - n) : ℂ) * u n) atTop (𝓝 0) := by
      simpa using hhead.sub_const (∑ n ∈ F, (chat (m - n) : ℂ) * u n)
    exact NormedAddGroup.tendsto_nhds_zero.mp h0 _ hδ
  filter_upwards [hheadev] with j hj
  rw [hsplit (v j) (hvsum j), hsplit u husum]
  set A := ∑ n ∈ F, (chat (m - n) : ℂ) * v j n with hA
  set B := ∑' n : ((↑F : Set ℤ)ᶜ : Set ℤ), (chat (m - ↑n) : ℂ) * v j ↑n with hB
  set C := ∑ n ∈ F, (chat (m - n) : ℂ) * u n with hC
  set D := ∑' n : ((↑F : Set ℤ)ᶜ : Set ℤ), (chat (m - ↑n) : ℂ) * u ↑n with hD
  have hb1 : ‖B‖ ≤ ε / 3 := htails (v j) (hvsum j) (hvbd j)
  have hb2 : ‖D‖ ≤ ε / 3 := htails u husum hubd
  have hrw : A + B - (C + D) = (A - C) + (B - D) := by ring
  rw [hrw]
  calc ‖(A - C) + (B - D)‖ ≤ ‖A - C‖ + ‖B - D‖ := norm_add_le _ _
    _ ≤ ‖A - C‖ + (‖B‖ + ‖D‖) := by linarith [norm_sub_le B D]
    _ < ε := by linarith

/-- `γ(s) ≤ Q_s(u)` for every admissible `u` with `normSq u = 1`. -/
lemma gam_le {s : ℝ} {u : ℤ → ℂ} (hu : MemDom u) (hn : normSq u = 1) :
    gam s ≤ Qform s u := by
  rw [gam_eq_gamTau, Qform_eq_Qtau]
  exact gamTau_le (sq_nonneg s) hu hn

/-- A minimizing sequence with explicit rate. -/
lemma exists_minimizing_seq (s : ℝ) :
    ∃ v : ℕ → ℤ → ℂ, (∀ j, MemDom (v j)) ∧ (∀ j, normSq (v j) = 1) ∧
      ∀ j : ℕ, Qform s (v j) < gam s + 1 / ((j : ℝ) + 1) := by
  have h : ∀ j : ℕ, ∃ u : ℤ → ℂ, MemDom u ∧ normSq u = 1
      ∧ Qform s u < gam s + 1 / ((j : ℝ) + 1) := by
    intro j
    have hε : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    obtain ⟨r, hrmem, hrlt⟩ := Real.lt_sInf_add_pos
      (⟨Qform s wit, wit, memDom_wit, normSq_wit, rfl⟩ :
        Set.Nonempty {r : ℝ | ∃ u : ℤ → ℂ, MemDom u ∧ normSq u = 1
          ∧ Qform s u = r}) hε
    obtain ⟨u, hu, hn, rfl⟩ := hrmem
    exact ⟨u, hu, hn, hrlt⟩
  choose v h1 h2 h3 using h
  exact ⟨v, h1, h2, h3⟩

/-! ### Minimizer existence, `γ`-comparison and continuity -/

/-- Existence of a normalized minimizer for positive `s` (direct method: minimizing sequences
have `Σ σ₊‖u‖²` bounded, hence uniformly small tails, hence an `ℓ²`-convergent
subsequence; conclude by coordinatewise convergence of `convS` and Fatou). -/
theorem exists_minimizer {s : ℝ} (hs : 0 < s) :
    ∃ u : ℤ → ℂ, MemDom u ∧ normSq u = 1 ∧ Qform s u = gam s := by
  obtain ⟨v, hvdom, hvnorm, hvlt⟩ := exists_minimizing_seq s
  have hvsum : ∀ j, Summable fun n : ℤ => ‖v j n‖ ^ 2 :=
    fun j => summable_normSq (hvdom j).1
  have hvbd1 : ∀ j, (∑' n : ℤ, ‖v j n‖ ^ 2) ≤ 1 := fun j => le_of_eq (hvnorm j)
  -- `Qform` tends to `gam` along the minimizing sequence
  have hQten : Tendsto (fun j => Qform s (v j)) atTop (𝓝 (gam s)) := by
    have hup : ∀ j : ℕ, Qform s (v j) ≤ gam s + 1 / ((j : ℝ) + 1) :=
      fun j => le_of_lt (hvlt j)
    have hlow : ∀ j : ℕ, gam s ≤ Qform s (v j) :=
      fun j => gam_le (hvdom j) (hvnorm j)
    have hub : Tendsto (fun j : ℕ => gam s + 1 / ((j : ℝ) + 1)) atTop
        (𝓝 (gam s)) := by
      have h2 : Tendsto (fun j : ℕ => gam s + 1 / ((j : ℝ) + 1)) atTop
          (𝓝 (gam s + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [add_zero] at h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub hlow hup
  -- uniform energy bound and coercivity along the sequence
  have hQbd : ∀ j, Qform s (v j) ≤ gam s + 1 := by
    intro j
    have h1 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have h0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      linarith
    linarith [hvlt j]
  have hCoer : ∀ j, (∑' n : ℤ, |6 * (n : ℝ) + 1| * ‖v j n‖ ^ 2) ≤ gam s + 5 := by
    intro j
    have h1 := tsum_weight_le (hvdom j)
    rw [hvnorm j] at h1
    have h2 : (∑' n : ℤ, sigP n * ‖v j n‖ ^ 2) ≤ Qform s (v j) := by
      have h3 : (0:ℝ) ≤ s ^ 2 * ∑' m : ℤ, sigM m * ‖convS (v j) m‖ ^ 2 :=
        mul_nonneg (sq_nonneg s)
          (tsum_nonneg fun m => mul_nonneg (sigM_nonneg m) (sq_nonneg _))
      rw [Qform]
      linarith
    linarith [hQbd j]
  -- coefficients lie in the closed unit ball; extract a pointwise limit
  have hmem : ∀ j, v j ∈ Set.pi Set.univ
      (fun _ : ℤ => Metric.closedBall (0 : ℂ) 1) := by
    intro j
    refine Set.mem_univ_pi.mpr fun n => ?_
    rw [mem_closedBall_zero_iff]
    have h1 : ‖v j n‖ ^ 2 ≤ 1 :=
      ((hvsum j).le_tsum n fun i _ => sq_nonneg _).trans (hvbd1 j)
    nlinarith [norm_nonneg (v j n)]
  have hcpt : IsCompact (Set.pi Set.univ
      fun _ : ℤ => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨u, -, φ, hφmono, hφten⟩ := hcpt.tendsto_subseq hmem
  have hpt : ∀ n : ℤ, Tendsto (fun j => v (φ j) n) atTop (𝓝 (u n)) :=
    fun n => tendsto_pi_nhds.mp hφten n
  have hQten2 : Tendsto (fun j => Qform s (v (φ j))) atTop (𝓝 (gam s)) :=
    hQten.comp hφmono.tendsto_atTop
  -- `ℓ²` control of the limit
  have hfin1 : ∀ F : Finset ℤ, (∑ n ∈ F, ‖u n‖ ^ 2) ≤ 1 := by
    intro F
    have hten : Tendsto (fun j => ∑ n ∈ F, ‖v (φ j) n‖ ^ 2) atTop
        (𝓝 (∑ n ∈ F, ‖u n‖ ^ 2)) :=
      tendsto_finsetSum _ fun n _ => (hpt n).norm.pow 2
    refine le_of_tendsto hten (Eventually.of_forall fun j => ?_)
    exact (Summable.sum_le_tsum F (fun i _ => sq_nonneg _) (hvsum (φ j))).trans
      (hvbd1 (φ j))
  have husum : Summable fun n : ℤ => ‖u n‖ ^ 2 :=
    summable_of_sum_le (fun n => sq_nonneg _) hfin1
  have hubd : (∑' n : ℤ, ‖u n‖ ^ 2) ≤ 1 := husum.tsum_le_of_sum_le hfin1
  -- coordinatewise convergence of the convolution
  have hcten : ∀ m : ℤ, Tendsto (fun j => convS (v (φ j)) m) atTop
      (𝓝 (convS u m)) :=
    fun m => tendsto_convS hpt (fun j => hvsum (φ j)) (fun j => hvbd1 (φ j))
      husum hubd m
  -- the key finset inequality in the limit
  have hkey : ∀ F : Finset ℤ, 0 ∈ F → ∀ G : Finset ℤ,
      (∑ n ∈ F, sigP n * ‖u n‖ ^ 2)
        + s ^ 2 * ∑ m ∈ G, sigM m * ‖convS u m‖ ^ 2 ≤ gam s := by
    intro F hF G
    have hten : Tendsto (fun j => (∑ n ∈ F, sigP n * ‖v (φ j) n‖ ^ 2)
        + s ^ 2 * ∑ m ∈ G, sigM m * ‖convS (v (φ j)) m‖ ^ 2) atTop
        (𝓝 ((∑ n ∈ F, sigP n * ‖u n‖ ^ 2)
          + s ^ 2 * ∑ m ∈ G, sigM m * ‖convS u m‖ ^ 2)) := by
      refine Tendsto.add ?_ ?_
      · exact tendsto_finsetSum _ fun n _ => ((hpt n).norm.pow 2).const_mul _
      · exact (tendsto_finsetSum _ fun m _ =>
          ((hcten m).norm.pow 2).const_mul _).const_mul _
    refine le_of_tendsto_of_tendsto' hten hQten2 fun j => ?_
    have h1 : (∑ n ∈ F, sigP n * ‖v (φ j) n‖ ^ 2)
        ≤ ∑' n : ℤ, sigP n * ‖v (φ j) n‖ ^ 2 := by
      refine Summable.sum_le_tsum F (fun i hi => ?_)
        (summable_sigP_mul (hvdom (φ j)).1)
      have hi0 : i ≠ 0 := fun h => hi (h ▸ hF)
      exact mul_nonneg (le_trans (by norm_num) (sigP_ge_of_ne_zero hi0))
        (sq_nonneg _)
    have h2 : (∑ m ∈ G, sigM m * ‖convS (v (φ j)) m‖ ^ 2)
        ≤ ∑' m : ℤ, sigM m * ‖convS (v (φ j)) m‖ ^ 2 :=
      Summable.sum_le_tsum G
        (fun i _ => mul_nonneg (sigM_nonneg i) (sq_nonneg _))
        (summable_sigM_mul (hvdom (φ j)).2)
    have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg s)
    rw [Qform]
    linarith
  -- `MemDom` of the limit, `+` side
  have hfinP : ∀ F : Finset ℤ, (∑ n ∈ F, |6 * (n : ℝ) + 1| * ‖u n‖ ^ 2)
      ≤ gam s + 4 := by
    intro F
    have h1 : (∑ n ∈ F, |6 * (n : ℝ) + 1| * ‖u n‖ ^ 2)
        ≤ ∑ n ∈ insert 0 F, |6 * (n : ℝ) + 1| * ‖u n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert 0 F)
        fun i _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
    have h2 : (∑ n ∈ insert 0 F, |6 * (n : ℝ) + 1| * ‖u n‖ ^ 2)
        ≤ ∑ n ∈ insert 0 F, (sigP n * ‖u n‖ ^ 2 + 4 * ‖u n‖ ^ 2) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have := weight_le_sigP_add_four i
      nlinarith [sq_nonneg ‖u i‖]
    rw [Finset.sum_add_distrib] at h2
    have h3 := hkey (insert 0 F) (Finset.mem_insert_self 0 F) ∅
    simp only [Finset.sum_empty, mul_zero, add_zero] at h3
    have h4 : (∑ n ∈ insert 0 F, 4 * ‖u n‖ ^ 2) ≤ 4 := by
      rw [← Finset.mul_sum]
      have := hfin1 (insert 0 F)
      linarith
    linarith
  have husumP : Summable fun n : ℤ => |6 * (n : ℝ) + 1| * ‖u n‖ ^ 2 :=
    summable_of_sum_le (fun n => mul_nonneg (abs_nonneg _) (sq_nonneg _)) hfinP
  -- `MemDom` of the limit, `-` side
  have hfinM : ∀ G : Finset ℤ, (∑ m ∈ G, sigM m * ‖convS u m‖ ^ 2)
      ≤ (gam s + 3) / s ^ 2 := by
    intro G
    have h3 := hkey {0} (Finset.mem_singleton_self 0) G
    rw [Finset.sum_singleton] at h3
    have h0 : sigP 0 = -3 := by norm_num [sigP]
    rw [h0] at h3
    have hu0 : ‖u 0‖ ^ 2 ≤ 1 :=
      (husum.le_tsum 0 fun i _ => sq_nonneg _).trans hubd
    have hs2 : (0:ℝ) < s ^ 2 := by positivity
    rw [le_div_iff₀ hs2]
    nlinarith
  have husumM : Summable fun m : ℤ => sigM m * ‖convS u m‖ ^ 2 :=
    summable_of_sum_le (fun m => mul_nonneg (sigM_nonneg m) (sq_nonneg _)) hfinM
  have hconvsq : Summable fun m : ℤ => ‖convS u m‖ ^ 2 := by
    have hind : Summable (fun m : ℤ =>
        if m = -1 then ‖convS u (-1)‖ ^ 2 else 0) := by
      apply summable_of_ne_finset_zero (s := ({-1} : Finset ℤ))
      intro b hb
      simp only [Finset.mem_singleton] at hb
      simp [hb]
    refine ((husumM.mul_left (1/3)).add hind).of_nonneg_of_le
      (fun m => sq_nonneg _) fun m => ?_
    rcases eq_or_ne m (-1) with rfl | hm
    · simp [sigM_neg_one]
    · have h3 := sigM_ge_three_of_ne hm
      simp only [if_neg hm, add_zero]
      nlinarith [sq_nonneg ‖convS u m‖]
  have husumMw : Summable fun m : ℤ => |6 * (m : ℝ) + 4| * ‖convS u m‖ ^ 2 := by
    refine (husumM.add (hconvsq.mul_left 2)).of_nonneg_of_le
      (fun m => mul_nonneg (abs_nonneg _) (sq_nonneg _)) fun m => ?_
    have := weight_le_sigM_add_two m
    nlinarith [sq_nonneg ‖convS u m‖]
  have hudom : MemDom u := ⟨husumP, husumMw⟩
  -- no mass escapes: `normSq u = 1`
  have habs_ge : ∀ (N : ℕ) (n : ℤ), n ∉ Finset.Icc (-(N:ℤ)) N →
      ((N:ℝ) + 1) ≤ |6 * (n : ℝ) + 1| := by
    intro N n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    have h : (N : ℤ) + 1 ≤ |6 * n + 1| := by
      rcases hn with h | h
      · rw [abs_of_neg (by omega : 6 * n + 1 < 0)]; omega
      · rw [abs_of_pos (by omega : 0 < 6 * n + 1)]; omega
    calc ((N:ℝ) + 1) = (((N + 1 : ℤ)) : ℝ) := by push_cast; ring
      _ ≤ ((|6 * n + 1| : ℤ) : ℝ) := by exact_mod_cast h
      _ = |6 * (n : ℝ) + 1| := by push_cast; norm_num
  have htailv : ∀ (j : ℕ) (N : ℕ),
      (∑' n : ((↑(Finset.Icc (-(N:ℤ)) N) : Set ℤ)ᶜ : Set ℤ), ‖v j ↑n‖ ^ 2)
        ≤ (gam s + 5) / ((N:ℝ) + 1) := by
    intro j N
    have hN1 : (0:ℝ) < (N:ℝ) + 1 := by positivity
    rw [le_div_iff₀ hN1]
    have hsub1 : Summable
        (fun n : ((↑(Finset.Icc (-(N:ℤ)) N) : Set ℤ)ᶜ : Set ℤ) =>
          ‖v j ↑n‖ ^ 2) := (hvsum j).subtype _
    have hsub2 : Summable
        (fun n : ((↑(Finset.Icc (-(N:ℤ)) N) : Set ℤ)ᶜ : Set ℤ) =>
          |6 * ((↑n : ℤ) : ℝ) + 1| * ‖v j ↑n‖ ^ 2) := ((hvdom j).1).subtype _
    have hle : (∑' n : ((↑(Finset.Icc (-(N:ℤ)) N) : Set ℤ)ᶜ : Set ℤ),
        ‖v j ↑n‖ ^ 2) * ((N:ℝ) + 1)
        ≤ ∑' n : ((↑(Finset.Icc (-(N:ℤ)) N) : Set ℤ)ᶜ : Set ℤ),
            |6 * ((↑n : ℤ) : ℝ) + 1| * ‖v j ↑n‖ ^ 2 := by
      rw [← tsum_mul_right]
      refine (hsub1.mul_right _).tsum_le_tsum (fun n => ?_) hsub2
      have hnot : (↑n : ℤ) ∉ Finset.Icc (-(N:ℤ)) N := by
        have h2 := n.2
        simpa using h2
      have hw := habs_ge N ↑n hnot
      nlinarith [sq_nonneg ‖v j (↑n : ℤ)‖]
    have hle2 : (∑' n : ((↑(Finset.Icc (-(N:ℤ)) N) : Set ℤ)ᶜ : Set ℤ),
        |6 * ((↑n : ℤ) : ℝ) + 1| * ‖v j ↑n‖ ^ 2)
        ≤ ∑' n : ℤ, |6 * (n : ℝ) + 1| * ‖v j n‖ ^ 2 :=
      Summable.tsum_subtype_le _ _
        (fun n => mul_nonneg (abs_nonneg _) (sq_nonneg _)) ((hvdom j).1)
    linarith [hCoer j]
  have hmass : ∀ N : ℕ, 1 - (gam s + 5) / ((N:ℝ) + 1)
      ≤ ∑ n ∈ Finset.Icc (-(N:ℤ)) N, ‖u n‖ ^ 2 := by
    intro N
    have hten : Tendsto
        (fun j => ∑ n ∈ Finset.Icc (-(N:ℤ)) N, ‖v (φ j) n‖ ^ 2)
        atTop (𝓝 (∑ n ∈ Finset.Icc (-(N:ℤ)) N, ‖u n‖ ^ 2)) :=
      tendsto_finsetSum _ fun n _ => (hpt n).norm.pow 2
    refine ge_of_tendsto hten (Eventually.of_forall fun j => ?_)
    have hsplit := (hvsum (φ j)).tsum_subtype_add_tsum_subtype_compl
      (↑(Finset.Icc (-(N:ℤ)) N) : Set ℤ)
    have hhead_eq : (∑' x : (↑(Finset.Icc (-(N:ℤ)) N) : Set ℤ),
        ‖v (φ j) ↑x‖ ^ 2)
        = ∑ n ∈ Finset.Icc (-(N:ℤ)) N, ‖v (φ j) n‖ ^ 2 :=
      Finset.tsum_subtype' (Finset.Icc (-(N:ℤ)) N)
        (fun n => ‖v (φ j) n‖ ^ 2)
    rw [hhead_eq] at hsplit
    have h1 : (∑' n : ℤ, ‖v (φ j) n‖ ^ 2) = 1 := hvnorm (φ j)
    have h2 := htailv (φ j) N
    linarith
  have hnormge : (1:ℝ) ≤ ∑' n : ℤ, ‖u n‖ ^ 2 := by
    have hlim : Tendsto (fun N : ℕ => 1 - (gam s + 5) / ((N:ℝ) + 1)) atTop
        (𝓝 1) := by
      have h2 : Tendsto (fun N : ℕ => (gam s + 5) * (1 / ((N:ℝ) + 1))) atTop
          (𝓝 ((gam s + 5) * 0)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
      rw [mul_zero] at h2
      have h3 : Tendsto (fun N : ℕ => 1 - (gam s + 5) * (1 / ((N:ℝ) + 1)))
          atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub h2
      rw [sub_zero] at h3
      have hfun : (fun N : ℕ => 1 - (gam s + 5) * (1 / ((N:ℝ) + 1)))
          = fun N : ℕ => 1 - (gam s + 5) / ((N:ℝ) + 1) := by
        funext N
        ring
      rwa [hfun] at h3
    refine le_of_tendsto hlim (Eventually.of_forall fun N => ?_)
    exact (hmass N).trans
      (Summable.sum_le_tsum _ (fun i _ => sq_nonneg _) husum)
  have hnormu : normSq u = 1 := le_antisymm hubd hnormge
  -- energy of the limit does not exceed `gam s`
  have hQle : Qform s u ≤ gam s := by
    have hhsP : Tendsto (fun F : Finset ℤ => ∑ n ∈ F, sigP n * ‖u n‖ ^ 2)
        atTop (𝓝 (∑' n : ℤ, sigP n * ‖u n‖ ^ 2)) :=
      (summable_sigP_mul husumP).hasSum
    have hhsM : Tendsto (fun G : Finset ℤ => ∑ m ∈ G, sigM m * ‖convS u m‖ ^ 2)
        atTop (𝓝 (∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2)) := husumM.hasSum
    have hstep1 : ∀ G : Finset ℤ,
        (∑' n : ℤ, sigP n * ‖u n‖ ^ 2)
          + s ^ 2 * ∑ m ∈ G, sigM m * ‖convS u m‖ ^ 2 ≤ gam s := by
      intro G
      refine le_of_tendsto (hhsP.add_const _) ?_
      filter_upwards [Filter.eventually_ge_atTop ({0} : Finset ℤ)] with F hF
      exact hkey F (Finset.singleton_subset_iff.mp hF) G
    refine le_of_tendsto ((hhsM.const_mul (s ^ 2)).const_add
      (∑' n : ℤ, sigP n * ‖u n‖ ^ 2)) (Eventually.of_forall hstep1)
  exact ⟨u, hudom, hnormu, le_antisymm hQle (gam_le hudom hnormu)⟩

/-- `γ(s) ≥ -3`, from `sigP_ge_neg_three` and `sigM_nonneg`.  (For the empty
infimum set, Mathlib's convention `sInf ∅ = 0` makes the bound trivial.) -/
theorem gam_ge_neg_three (s : ℝ) : -3 ≤ gam s := by
  rw [gam]
  rcases Set.eq_empty_or_nonempty
      {r : ℝ | ∃ u : ℤ → ℂ, MemDom u ∧ normSq u = 1 ∧ Qform s u = r} with h | h
  · rw [h, Real.sInf_empty]; norm_num
  · refine le_csInf h ?_
    rintro r ⟨u, hu, hnorm, rfl⟩
    have hl2 : Summable (fun n : ℤ => ‖u n‖ ^ 2) := summable_normSq hu.1
    have hsig := summable_sigP_mul hu.1
    have hpt : ∀ n : ℤ, -3 * ‖u n‖ ^ 2 ≤ sigP n * ‖u n‖ ^ 2 :=
      fun n => mul_le_mul_of_nonneg_right (sigP_ge_neg_three n) (sq_nonneg _)
    have h1 : -3 * ∑' n : ℤ, ‖u n‖ ^ 2 ≤ ∑' n : ℤ, sigP n * ‖u n‖ ^ 2 := by
      rw [← tsum_mul_left]
      exact (hl2.mul_left _).tsum_le_tsum hpt hsig
    have h2 : (0 : ℝ) ≤ s ^ 2 * ∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2 :=
      mul_nonneg (sq_nonneg s)
        (tsum_nonneg fun m => mul_nonneg (sigM_nonneg m) (sq_nonneg _))
    rw [normSq] at hnorm
    rw [hnorm] at h1
    rw [Qform]
    linarith

/-- Paper's `single_crossing`, continuity half: `γ` is continuous on `(0,∞)`
(infimum of functions affine in `s²` is concave in `s²`, hence continuous on
the open half-line). -/
theorem gam_continuousOn : ContinuousOn gam (Set.Ioi (0 : ℝ)) := by
  have hcont : ContinuousOn gamTau (Set.Ioi (0 : ℝ)) := by
    have h := gamTau_concaveOn.continuousOn_interior
    rwa [interior_Ici] at h
  have hmap : Set.MapsTo (fun s : ℝ => s ^ 2) (Set.Ioi 0) (Set.Ioi 0) := by
    intro s hs
    rw [Set.mem_Ioi] at hs ⊢
    positivity
  have hfun : gam = fun s : ℝ => gamTau (s ^ 2) := funext gam_eq_gamTau
  rw [hfun]
  simpa [Function.comp_def]
    using hcont.comp ((continuous_pow 2).continuousOn) hmap

/- Paper's `threshold_lower_bound`, `γ(1) < 0`, is proved in `GammaOne.lean`
(as `CircleQ.gam_one_neg`) directly from the m=2 arc test field — it needs
`TestField`/`SingleArc`, hence lives downstream of this file. -/

end KsIndex.CircleQ
