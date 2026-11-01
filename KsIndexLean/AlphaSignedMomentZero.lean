module

public import KsIndexLean.AlphaTrialReflection
public import KsIndexLean.PowerArcSignedTails
public import KsIndexLean.AlphaOppositeHalfIdentity

@[expose] public section


/-! # Vanishing of the signed convolution moment

For `0 < β ≤ 1`, the signed lattice sums are absolutely summable for every
real offset. Write `S c = ∑' n : ℕ, (-1)^n * g β (c + 2*n)` and
`D c = S c - S (2-c)`. Peeling the first term and using the evenness of `g`
gives `D (c+2) = -D c`. The anchors `D 0 = D 1 = 0`, followed by induction
in both directions, give vanishing at every integer offset.

Splitting the integer sum into `n` and `-(n+1)` identifies it with this defect.
The resulting identity extends by finite linear combination to
`familyConvolution`, with arbitrary integer shifts and real coefficients.
Applying it to the two families in the trial convolution proves
`∑' m : ℤ, (-1)^m * (convS trial m).re = 0`.

The module exports the summability statements needed for these rearrangements.
Its conclusions concern full infinite sums; no finite truncation or numerical
error estimate is used. -/

noncomputable section
namespace KsIndex.AlphaRemarkTrial
open PowerArc CircleQ

/-! ### Generic signed lattice sums -/

lemma summable_abs_g_shifted {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (c : ℝ) :
    Summable (fun n : ℕ => |g β (c + 2 * n)|) := by
  rw [← summable_nat_add_iff (Nat.ceil ((1 - c) / 2))]
  have hk : β ≤ c + 2 * (Nat.ceil ((1 - c) / 2) : ℝ) := by
    have h := Nat.le_ceil ((1 - c) / 2)
    linarith
  exact (abs_g_summable hβ hk).congr fun n => by
    congr 1
    push_cast
    ring

lemma summable_signed_g_nat {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (c : ℝ) :
    Summable (fun n : ℕ => (-1 : ℝ) ^ n * g β (c + 2 * n)) := by
  apply Summable.of_abs
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
    summable_abs_g_shifted hβ hβ1 c

/-- The one-sided signed lattice sum as a function of the offset. -/
def signedLattice (β c : ℝ) : ℝ := ∑' n : ℕ, (-1 : ℝ) ^ n * g β (c + 2 * n)

/-- The reflection defect of the one-sided signed sum. -/
def latticeDefect (β c : ℝ) : ℝ := signedLattice β c - signedLattice β (2 - c)

lemma signedLattice_peel {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (c : ℝ) :
    signedLattice β c = g β c - signedLattice β (c + 2) := by
  rw [signedLattice, (summable_signed_g_nat hβ hβ1 c).tsum_eq_zero_add]
  have hre : (fun n : ℕ => (-1 : ℝ) ^ (n + 1) * g β (c + 2 * ((n : ℕ) + 1 : ℕ))) =
      fun n : ℕ => -((-1 : ℝ) ^ n * g β ((c + 2) + 2 * n)) := by
    funext n
    rw [pow_succ]
    push_cast
    ring_nf
  simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero, add_zero]
  rw [hre, tsum_neg, signedLattice]
  ring

/-- The two-step defect recursion, from one peel on each side and `g_neg`. -/
lemma latticeDefect_step {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (c : ℝ) :
    latticeDefect β (c + 2) = -latticeDefect β c := by
  have hpc := signedLattice_peel hβ hβ1 c
  have hpn := signedLattice_peel hβ hβ1 (-c)
  have hg : g β (-c) = g β c := g_neg β c
  have e1 : (2 : ℝ) - (c + 2) = -c := by ring
  have e2 : -c + 2 = 2 - c := by ring
  rw [e2] at hpn
  rw [latticeDefect, latticeDefect, e1]
  linarith

lemma latticeDefect_step' {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (c : ℝ) :
    latticeDefect β (c - 2) = -latticeDefect β c := by
  have h := latticeDefect_step hβ hβ1 (c - 2)
  have e : c - 2 + 2 = c := by ring
  rw [e] at h
  linarith

/-- The even anchor: `latticeDefect β 0 = 0`. -/
lemma latticeDefect_zero {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    latticeDefect β 0 = 0 := by
  have h2 : signedLattice β 2 = (2 + β) * g β 2 / (2 * β) :=
    signed_g_tsum hβ (by norm_num) (by linarith)
  have hstep := g_step_two hβ 0
  norm_num at hstep
  have hpeel := signedLattice_peel hβ hβ1 0
  norm_num at hpeel
  rw [latticeDefect]
  norm_num
  rw [hpeel, h2]
  have hβ' : β ≠ 0 := ne_of_gt hβ
  field_simp
  linarith [hstep]

/-- The odd anchor: `latticeDefect β 1 = 0`. -/
lemma latticeDefect_one (β : ℝ) : latticeDefect β 1 = 0 := by
  rw [latticeDefect]
  norm_num

lemma latticeDefect_nat_up {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {c₀ : ℝ}
    (h0 : latticeDefect β c₀ = 0) : ∀ k : ℕ, latticeDefect β (c₀ + 2 * k) = 0 := by
  intro k
  induction k with
  | zero => simpa using h0
  | succ n ih =>
      have hs := latticeDefect_step hβ hβ1 (c₀ + 2 * n)
      rw [show c₀ + 2 * ((n : ℕ) + 1 : ℕ) = (c₀ + 2 * n) + 2 by push_cast; ring,
        hs, ih, neg_zero]

lemma latticeDefect_nat_down {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) {c₀ : ℝ}
    (h0 : latticeDefect β c₀ = 0) : ∀ k : ℕ, latticeDefect β (c₀ - 2 * k) = 0 := by
  intro k
  induction k with
  | zero => simpa using h0
  | succ n ih =>
      have hs := latticeDefect_step' hβ hβ1 (c₀ - 2 * n)
      rw [show c₀ - 2 * ((n : ℕ) + 1 : ℕ) = (c₀ - 2 * n) - 2 by push_cast; ring,
        hs, ih, neg_zero]

/-- The defect vanishes at every integer offset. -/
lemma latticeDefect_int {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (c : ℤ) :
    latticeDefect β c = 0 := by
  have hup0 := latticeDefect_nat_up hβ hβ1 (latticeDefect_zero hβ hβ1)
  have hdn0 := latticeDefect_nat_down hβ hβ1 (latticeDefect_zero hβ hβ1)
  have hup1 := latticeDefect_nat_up hβ hβ1 (latticeDefect_one β)
  have hdn1 := latticeDefect_nat_down hβ hβ1 (latticeDefect_one β)
  rcases Int.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    by_cases hm2 : (0 : ℤ) ≤ m
    · lift m to ℕ using hm2 with k
      have := hup0 k
      rw [show ((k : ℤ) + k : ℤ) = ((2 * k : ℤ)) by ring]
      rw [show (((2 * k : ℤ) : ℤ) : ℝ) = 0 + 2 * (k : ℝ) by push_cast; ring]
      exact this
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) := ⟨(-m).toNat, by omega⟩
      have := hdn0 k
      rw [show ((((-(k : ℤ)) + -(k : ℤ) : ℤ)) : ℝ) = 0 - 2 * (k : ℝ) by push_cast; ring]
      exact this
  · subst hm
    by_cases hm2 : (0 : ℤ) ≤ m
    · lift m to ℕ using hm2 with k
      have := hup1 k
      rw [show (((2 * (k : ℤ) + 1 : ℤ)) : ℝ) = 1 + 2 * (k : ℝ) by push_cast; ring]
      exact this
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) := ⟨(-m).toNat, by omega⟩
      have := hdn1 k
      rw [show (((2 * (-(k : ℤ)) + 1 : ℤ)) : ℝ) = 1 - 2 * (k : ℝ) by push_cast; ring]
      exact this

/-! ### The full signed lattice sum over `ℤ` -/

lemma negOne_zpow_neg_add_one (n : ℕ) :
    (-1 : ℝ) ^ (-((n : ℤ) + 1)) = -(-1 : ℝ) ^ n := by
  have h1 := KsIndex.OppositeHalf.negOne_zpow_sub (-(n : ℤ)) 1
  have h2 := KsIndex.OppositeHalf.negOne_zpow_sub 0 (n : ℤ)
  simp only [zpow_zero, one_mul, zero_sub] at h2
  rw [show -((n : ℤ) + 1) = -(n : ℤ) - 1 by ring, h1, h2, zpow_natCast]
  norm_num

lemma summable_signed_g_int {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (c : ℝ) :
    Summable (fun m : ℤ => (-1 : ℝ) ^ m * g β (2 * (m : ℝ) + c)) := by
  apply Summable.of_nat_of_neg_add_one
  · apply (summable_signed_g_nat hβ hβ1 c).congr
    intro n
    rw [zpow_natCast]
    congr 2
    push_cast
    ring
  · apply ((summable_signed_g_nat hβ hβ1 (2 - c)).neg).congr
    intro n
    rw [negOne_zpow_neg_add_one,
      show (2 * ((-((n : ℤ) + 1) : ℤ) : ℝ) + c) = -(((2 : ℝ) - c) + 2 * n) by
        push_cast; ring, g_neg]
    ring

/-- The signed lattice sum over all of `ℤ` vanishes at every integer offset. -/
theorem tsum_signed_g_int {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (c : ℤ) :
    ∑' m : ℤ, (-1 : ℝ) ^ m * g β (2 * (m : ℝ) + c) = 0 := by
  have hsum := summable_signed_g_int hβ hβ1 (c : ℝ)
  rw [← tsum_nat_add_neg_add_one hsum]
  have hA := summable_signed_g_nat hβ hβ1 ((c : ℤ) : ℝ)
  have hB := summable_signed_g_nat hβ hβ1 ((2 : ℝ) - c)
  have hpair : (fun n : ℕ =>
      ((-1 : ℝ) ^ ((n : ℤ)) * g β (2 * (((n : ℤ)) : ℝ) + c)) +
      ((-1 : ℝ) ^ (-((n : ℤ) + 1)) * g β (2 * ((-((n : ℤ) + 1) : ℤ) : ℝ) + c))) =
      fun n : ℕ => ((-1 : ℝ) ^ n * g β (((c : ℤ) : ℝ) + 2 * n)) -
        ((-1 : ℝ) ^ n * g β (((2 : ℝ) - c) + 2 * n)) := by
    funext n
    rw [negOne_zpow_neg_add_one, zpow_natCast,
      show (2 * ((-((n : ℤ) + 1) : ℤ) : ℝ) + c) = -(((2 : ℝ) - c) + 2 * n) by
        push_cast; ring, g_neg,
      show (2 * (((n : ℤ)) : ℝ) + ((c : ℤ) : ℝ)) = (((c : ℤ)) : ℝ) + 2 * n by
        push_cast; ring]
    ring
  rw [hpair, hA.tsum_sub hB]
  have := latticeDefect_int hβ hβ1 c
  rw [latticeDefect, signedLattice, signedLattice] at this
  exact this

/-! ### Application to the trial families -/

lemma summable_signed_family {ι : Type*} [Fintype ι] {β : ℝ} (hβ : 0 < β)
    (hβ1 : β ≤ 1) (d : ι → ℤ) (a : ι → ℝ) :
    Summable (fun m : ℤ => (-1 : ℝ) ^ m * familyConvolution β d a m) := by
  have hc : (fun m : ℤ => (-1 : ℝ) ^ m * familyConvolution β d a m) =
      fun m : ℤ => ∑ i, (a i / g β 0) *
        ((-1 : ℝ) ^ m * g β (2 * (m : ℝ) + ((d i : ℝ) + 1))) := by
    funext m
    rw [familyConvolution, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hc]
  exact summable_sum fun i _ =>
    (summable_signed_g_int hβ hβ1 ((d i : ℝ) + 1)).mul_left _

/-- The signed moment of a trial family vanishes. -/
theorem tsum_signed_family {ι : Type*} [Fintype ι] {β : ℝ} (hβ : 0 < β)
    (hβ1 : β ≤ 1) (d : ι → ℤ) (a : ι → ℝ) :
    ∑' m : ℤ, (-1 : ℝ) ^ m * familyConvolution β d a m = 0 := by
  have hc : (fun m : ℤ => (-1 : ℝ) ^ m * familyConvolution β d a m) =
      fun m : ℤ => ∑ i, (a i / g β 0) *
        ((-1 : ℝ) ^ m * g β (2 * (m : ℝ) + ((d i : ℝ) + 1))) := by
    funext m
    rw [familyConvolution, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hc, Summable.tsum_finsetSum fun i _ =>
    (summable_signed_g_int hβ hβ1 ((d i : ℝ) + 1)).mul_left _]
  apply Finset.sum_eq_zero
  intro i _
  rw [tsum_mul_left]
  have h0 : ∑' m : ℤ, (-1 : ℝ) ^ m * g β (2 * (m : ℝ) + ((d i : ℝ) + 1)) = 0 := by
    have := tsum_signed_g_int hβ hβ1 (d i + 1)
    rw [show ((d i + 1 : ℤ) : ℝ) = (d i : ℝ) + 1 by push_cast; ring] at this
    exact this
  rw [h0, mul_zero]

lemma summable_signed_convolutionA :
    Summable (fun m : ℤ => (-1 : ℝ) ^ m * convolutionA m) :=
  summable_signed_family (by norm_num) (by norm_num) _ _

lemma summable_signed_convolutionB :
    Summable (fun m : ℤ => (-1 : ℝ) ^ m * convolutionB m) :=
  summable_signed_family (by norm_num) (by norm_num) _ _

/-- `Z = 0`: the signed moment of the actual trial convolution
vanishes exactly. -/
theorem tsum_signed_convS_trial_re :
    ∑' m : ℤ, (-1 : ℝ) ^ m * (convS trial m).re = 0 := by
  have hc : (fun m : ℤ => (-1 : ℝ) ^ m * (convS trial m).re) =
      fun m : ℤ => ((-1 : ℝ) ^ m * convolutionA m) +
        ((-1 : ℝ) ^ m * convolutionB m) := by
    funext m
    rw [convS_trial_re_eq_families]
    ring
  rw [hc, summable_signed_convolutionA.tsum_add summable_signed_convolutionB]
  have hA0 : ∑' m : ℤ, (-1 : ℝ) ^ m * convolutionA m = 0 := by
    unfold convolutionA
    exact tsum_signed_family (by norm_num) (by norm_num) _ _
  have hB0 : ∑' m : ℤ, (-1 : ℝ) ^ m * convolutionB m = 0 := by
    unfold convolutionB
    exact tsum_signed_family (by norm_num) (by norm_num) _ _
  rw [hA0, hB0, add_zero]

end KsIndex.AlphaRemarkTrial
