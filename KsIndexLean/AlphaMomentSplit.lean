module

public import KsIndexLean.AlphaSignedMomentZero

@[expose] public section


/-! Opposite-half summation and the signed moment decomposition.

The summation identities apply to a real sequence `v` with summable absolute
values. Separate lemmas establish convergence of each series and justify the
integer-to-half-line reindexing.

`tsum_split` sums the pointwise opposite-half identity over the full integer
lattice. `tsum_V_split` expresses the signed moment as the finite prefix
`m = -4..3` plus `(momentKa v + momentKb v)/6`, with half-line denominators
shifted by `14/3` and `13/3`. The final lemma supplies the absolute summability
hypothesis for the real part of the concrete trial's convolution. -/

noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ Real

/-! ### Kernel bounds -/

lemma abs_negOne_zpow (d : ℤ) : |(-1 : ℝ) ^ d| = 1 := by
  rcases Int.even_or_odd d with h | h
  · rw [h.neg_one_zpow]; norm_num
  · rw [Odd.neg_one_zpow h]; norm_num

lemma abs_chat (d : ℤ) : |chat d| = 2 / π / |2 * (d : ℝ) + 1| := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rw [chat, abs_div, abs_mul, abs_negOne_zpow, mul_one, abs_div, abs_two,
    abs_of_pos hπ]

lemma one_le_abs_odd (d : ℤ) : (1 : ℝ) ≤ |2 * (d : ℝ) + 1| := by
  have h : (1 : ℤ) ≤ |2 * d + 1| := Int.one_le_abs (by omega)
  calc (1 : ℝ) ≤ ((|2 * d + 1| : ℤ) : ℝ) := by exact_mod_cast h
    _ = |2 * (d : ℝ) + 1| := by rw [Int.cast_abs]; push_cast; ring_nf

lemma abs_sigM_chat_le (n m : ℤ) :
    |sigM m * chat (m - n)| ≤ 2 / π * (3 + |6 * (n : ℝ) + 1|) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h1 : (1 : ℝ) ≤ |2 * ((m : ℝ) - n) + 1| := by
    have := one_le_abs_odd (m - n)
    rwa [show ((m - n : ℤ) : ℝ) = (m : ℝ) - n by push_cast; ring] at this
  have hd : (0 : ℝ) < |2 * ((m : ℝ) - n) + 1| := lt_of_lt_of_le one_pos h1
  have hsig : |sigM m| ≤ |6 * (m : ℝ) + 4| := abs_sigM_le m
  have hM : |6 * (m : ℝ) + 4| ≤ 3 * |2 * ((m : ℝ) - n) + 1| + |6 * (n : ℝ) + 1| := by
    calc |6 * (m : ℝ) + 4| = |3 * (2 * ((m : ℝ) - n) + 1) + (6 * (n : ℝ) + 1)| := by
          congr 1; ring
      _ ≤ |3 * (2 * ((m : ℝ) - n) + 1)| + |6 * (n : ℝ) + 1| := abs_add_le _ _
      _ = 3 * |2 * ((m : ℝ) - n) + 1| + |6 * (n : ℝ) + 1| := by
          rw [abs_mul]; norm_num
  have hchat : |chat (m - n)| = 2 / π / |2 * ((m : ℝ) - n) + 1| := by
    have := abs_chat (m - n)
    rwa [show ((m - n : ℤ) : ℝ) = (m : ℝ) - n by push_cast; ring] at this
  have hbound : |sigM m| / |2 * ((m : ℝ) - n) + 1| ≤ 3 + |6 * (n : ℝ) + 1| := by
    rw [div_le_iff₀ hd]
    calc |sigM m| ≤ |6 * (m : ℝ) + 4| := hsig
      _ ≤ 3 * |2 * ((m : ℝ) - n) + 1| + |6 * (n : ℝ) + 1| := hM
      _ ≤ (3 + |6 * (n : ℝ) + 1|) * |2 * ((m : ℝ) - n) + 1| := by
          nlinarith [abs_nonneg (6 * (n : ℝ) + 1)]
  calc |sigM m * chat (m - n)| = |sigM m| * (2 / π / |2 * ((m : ℝ) - n) + 1|) := by
        rw [abs_mul, hchat]
    _ = 2 / π * (|sigM m| / |2 * ((m : ℝ) - n) + 1|) := by ring
    _ ≤ 2 / π * (3 + |6 * (n : ℝ) + 1|) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)

/-! ### Summability for sequences with summable absolute values -/

variable {v : ℤ → ℝ} (hv : Summable (fun m : ℤ => |v m|))

include hv in
lemma summable_transpose (n : ℤ) :
    Summable (fun m : ℤ => sigM m * chat (m - n) * v m) := by
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun m => abs_nonneg _)
    (fun m => ?_) (hv.mul_left (2 / π * (3 + |6 * (n : ℝ) + 1|)))
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_sigM_chat_le n m) (abs_nonneg _)

include hv in
lemma summable_kernel (n : ℤ) :
    Summable (fun m : ℤ => chat (m - n) * v m) := by
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun m => abs_nonneg _)
    (fun m => ?_) (hv.mul_left (2 / π))
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have hc := abs_chat (m - n)
  have h1 := one_le_abs_odd (m - n)
  have hπ : (0 : ℝ) < π := Real.pi_pos
  rw [hc, div_le_iff₀ (lt_of_lt_of_le one_pos h1)]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 / π)]

include hv in
lemma summable_opposite (n : ℤ) :
    Summable (fun m : ℤ =>
      if (6 * n + 1) * (6 * m + 4) < 0 then sigM m * chat (m - n) * v m else 0) := by
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun m => abs_nonneg _)
    (fun m => ?_) ((summable_transpose hv n).abs)
  by_cases hc : (6 * n + 1) * (6 * m + 4) < 0
  · rw [if_pos hc]
  · rw [if_neg hc, abs_zero]
    exact abs_nonneg _

include hv in
lemma summable_signed_v : Summable (fun m : ℤ => (-1 : ℝ) ^ m * v m) := by
  apply Summable.of_abs
  exact hv.congr fun m => by rw [abs_mul, abs_negOne_zpow, one_mul]

include hv in
lemma summable_signed_moment_v :
    Summable (fun m : ℤ => (-1 : ℝ) ^ m * v m / (6 * (m : ℝ) + 4)) := by
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun m => abs_nonneg _)
    (fun m => ?_) (hv.mul_left (1 / 2))
  have h2 : (2 : ℝ) ≤ |6 * (m : ℝ) + 4| := by
    have h : (2 : ℤ) ≤ |6 * m + 4| := by
      rcases le_or_gt 0 m with h | h
      · rw [abs_of_nonneg (by omega)]; omega
      · rw [abs_of_neg (by omega)]; omega
    calc (2 : ℝ) ≤ ((|6 * m + 4| : ℤ) : ℝ) := by exact_mod_cast h
      _ = |6 * (m : ℝ) + 4| := by rw [Int.cast_abs]; push_cast; ring_nf
  rw [abs_div, abs_mul, abs_negOne_zpow, one_mul,
    div_le_iff₀ (lt_of_lt_of_le two_pos h2)]
  nlinarith [abs_nonneg (v m)]

/-! ### The full-sum opposite-half identity -/

include hv in
/-- The opposite-half identity for full sums, with absolute convergence
of each series established by the preceding lemmas. -/
theorem tsum_split (n : ℤ) :
    (∑' m : ℤ, sigM m * chat (m - n) * v m) =
      sigP n * (∑' m : ℤ, chat (m - n) * v m)
      + 2 * (∑' m : ℤ, if (6 * n + 1) * (6 * m + 4) < 0
          then sigM m * chat (m - n) * v m else 0)
      + 6 * oppSign n / π * (-1 : ℝ) ^ n * (∑' m : ℤ, (-1 : ℝ) ^ m * v m)
      + 24 / (π * |6 * (n : ℝ) + 1|) * (-1 : ℝ) ^ n *
          (∑' m : ℤ, (-1 : ℝ) ^ m * v m / (6 * (m : ℝ) + 4)) := by
  have h1 := summable_kernel hv n
  have h2 := summable_opposite hv n
  have h3 := summable_signed_v hv
  have h4 := summable_signed_moment_v hv
  have hpt : (fun m : ℤ => sigM m * chat (m - n) * v m) =
      fun m : ℤ => sigP n * (chat (m - n) * v m)
        + 2 * (if (6 * n + 1) * (6 * m + 4) < 0
            then sigM m * chat (m - n) * v m else 0)
        + 6 * oppSign n / π * (-1 : ℝ) ^ n * ((-1 : ℝ) ^ m * v m)
        + 24 / (π * |6 * (n : ℝ) + 1|) * (-1 : ℝ) ^ n *
            ((-1 : ℝ) ^ m * v m / (6 * (m : ℝ) + 4)) := by
    funext m
    have h := pointwise_split n m
    by_cases hc : (6 * n + 1) * (6 * m + 4) < 0
    · rw [if_pos hc] at h
      rw [if_pos hc]
      linear_combination (v m) * h
    · rw [if_neg hc] at h
      rw [if_neg hc]
      linear_combination (v m) * h
  rw [hpt,
    (((h1.mul_left _).add (h2.mul_left _)).add (h3.mul_left _)).tsum_add
      (h4.mul_left _),
    ((h1.mul_left _).add (h2.mul_left _)).tsum_add (h3.mul_left _),
    (h1.mul_left _).tsum_add (h2.mul_left _),
    tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left]

/-! ### The signed moment prefix and half-line decomposition -/

/-- Upper half-line moment at `z = 14/3` (samples `m = 4 + k`). -/
def momentKa (v : ℤ → ℝ) : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ k * v (4 + k) / ((k : ℝ) + 14/3)

/-- Lower half-line moment at `z = 13/3` (samples `m = -5 - k`). -/
def momentKb (v : ℤ → ℝ) : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ k * v (-5 - k) / ((k : ℝ) + 13/3)

include hv in
lemma summable_momentKa :
    Summable (fun k : ℕ => (-1 : ℝ) ^ k * v (4 + k) / ((k : ℝ) + 14/3)) := by
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    (hv.comp_injective (fun a b h => by simp only at h; omega : Function.Injective
      (fun k : ℕ => (4 + k : ℤ))))
  simp only [Function.comp_def]
  have hz : (0 : ℝ) < (k : ℝ) + 14/3 := by positivity
  have h1 : (1 : ℝ) ≤ (k : ℝ) + 14/3 := by
    have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hz, div_le_iff₀ hz]
  nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg (v (4 + (k : ℤ))))]

include hv in
lemma summable_momentKb :
    Summable (fun k : ℕ => (-1 : ℝ) ^ k * v (-5 - k) / ((k : ℝ) + 13/3)) := by
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    (hv.comp_injective (fun a b h => by simp only at h; omega : Function.Injective
      (fun k : ℕ => (-5 - k : ℤ))))
  simp only [Function.comp_def]
  have hz : (0 : ℝ) < (k : ℝ) + 13/3 := by positivity
  have h1 : (1 : ℝ) ≤ (k : ℝ) + 13/3 := by
    have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hz, div_le_iff₀ hz]
  nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg (v (-5 - (k : ℤ))))]

include hv in
/-- The signed moment splits into the finite prefix `m = -4..3` plus
`(momentKa v + momentKb v)/6`; summability justifies the reindexing. -/
theorem tsum_V_split :
    (∑' m : ℤ, (-1 : ℝ) ^ m * v m / (6 * (m : ℝ) + 4)) =
      ((∑ k ∈ Finset.range 4,
          (-1 : ℝ) ^ (k : ℤ) * v (k : ℤ) / (6 * (((k : ℤ)) : ℝ) + 4))
        + ∑ k ∈ Finset.range 4,
            (-1 : ℝ) ^ (-((k : ℤ) + 1)) * v (-((k : ℤ) + 1)) /
              (6 * (((-((k : ℤ) + 1) : ℤ)) : ℝ) + 4))
      + (momentKa v + momentKb v) / 6 := by
  classical
  set f : ℤ → ℝ := fun m => (-1 : ℝ) ^ m * v m / (6 * (m : ℝ) + 4) with hf
  have hfs := summable_signed_moment_v hv
  have hpos : Summable (fun k : ℕ => f ((k : ℤ))) :=
    hfs.comp_injective (fun a b h => by exact_mod_cast h)
  have hneg : Summable (fun k : ℕ => f (-((k : ℤ) + 1))) :=
    hfs.comp_injective (fun a b h => by simp only at h; omega : Function.Injective
      (fun k : ℕ => -((k : ℤ) + 1)))
  have hsplit : (∑' m : ℤ, f m) =
      (∑' k : ℕ, f ((k : ℤ))) + ∑' k : ℕ, f (-((k : ℤ) + 1)) :=
    (HasSum.of_nat_of_neg_add_one hpos.hasSum hneg.hasSum).tsum_eq
  rw [hsplit, ← hpos.sum_add_tsum_nat_add 4, ← hneg.sum_add_tsum_nat_add 4]
  have hKa : (∑' k : ℕ, f (((k + 4 : ℕ) : ℤ))) = momentKa v / 6 := by
    rw [momentKa, ← tsum_div_const]
    apply tsum_congr
    intro k
    simp only [hf]
    have hz : (-1 : ℝ) ^ (((k + 4 : ℕ) : ℤ)) = (-1 : ℝ) ^ k := by
      rw [zpow_natCast, pow_add]
      norm_num
    rw [hz, show (((k + 4 : ℕ) : ℤ)) = (4 + (k : ℤ)) by push_cast; ring,
      show (6 * (((4 + (k : ℤ)) : ℤ) : ℝ) + 4) = 6 * ((k : ℝ) + 14/3) by
        push_cast; ring]
    rw [div_div]
    congr 1
    ring
  have hKb : (∑' k : ℕ, f (-(((k + 4 : ℕ) : ℤ)) - 1)) = momentKb v / 6 := by
    rw [momentKb, ← tsum_div_const]
    apply tsum_congr
    intro k
    simp only [hf]
    have hz : (-1 : ℝ) ^ (-(((k + 4 : ℕ) : ℤ)) - 1) = -(-1 : ℝ) ^ k := by
      rw [show (-(((k + 4 : ℕ) : ℤ)) - 1) = -((((k + 4 : ℕ) : ℤ)) + 1) by ring,
        KsIndex.AlphaRemarkTrial.negOne_zpow_neg_add_one (k + 4), pow_add]
      norm_num
    rw [hz, show (-(((k + 4 : ℕ) : ℤ)) - 1) = (-5 - (k : ℤ)) by push_cast; ring,
      show (6 * (((-5 - (k : ℤ) : ℤ)) : ℝ) + 4) = -(6 * ((k : ℝ) + 13/3)) by
        push_cast; ring]
    have hzk : ((k : ℝ) + 13/3) ≠ 0 := by positivity
    field_simp
  have htail : (∑' k : ℕ, f (-(((k + 4 : ℕ) : ℤ) + 1))) =
      (∑' k : ℕ, f (-(((k + 4 : ℕ) : ℤ)) - 1)) := by
    apply tsum_congr
    intro k
    congr 1
  rw [hKa, htail, hKb]
  simp only [hf]
  ring

/-! ### Trial instantiation -/

open KsIndex.AlphaRemarkTrial in
lemma summable_abs_g_int' {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (c : ℝ) :
    Summable (fun m : ℤ => |PowerArc.g β (2 * (m : ℝ) + c)|) := by
  apply Summable.of_nat_of_neg_add_one
  · apply (summable_abs_g_shifted hβ hβ1 c).congr
    intro n
    congr 2
    push_cast
    ring
  · apply (summable_abs_g_shifted hβ hβ1 (2 - c)).congr
    intro n
    rw [show ((2 : ℝ) - c + 2 * n) = -(2 * ((-((n : ℤ) + 1) : ℤ) : ℝ) + c) by
      push_cast; ring, PowerArc.g_neg]

open KsIndex.AlphaRemarkTrial in
/-- The concrete trial's convolution has summable absolute real parts —
the `ℓ¹` input instantiating this module for the actual trial. -/
lemma summable_abs_convS_trial_re :
    Summable (fun m : ℤ => |(convS trial m).re|) := by
  have hb : (0 : ℝ) < 4323618/10000000 := by norm_num
  have hb1 : (4323618/10000000 : ℝ) ≤ 1 := by norm_num
  have hc : (0 : ℝ) < 5676382/10000000 := by norm_num
  have hc1 : (5676382/10000000 : ℝ) ≤ 1 := by norm_num
  have hfam : ∀ {ι : Type} [Fintype ι] (β : ℝ), 0 < β → β ≤ 1 →
      ∀ (d : ι → ℤ) (a : ι → ℝ),
      Summable (fun m : ℤ => |familyConvolution β d a m|) := by
    intro ι _ β hβ hβ1 d a
    apply Summable.of_nonneg_of_le (fun m => abs_nonneg _) (fun m => ?_)
      (summable_sum (s := Finset.univ) fun i _ =>
        ((summable_abs_g_int' hβ hβ1 ((d i : ℝ) + 1)).mul_left |a i / PowerArc.g β 0|))
    rw [familyConvolution]
    calc |∑ i, a i * (PowerArc.g β (2 * (m : ℝ) + d i + 1) / PowerArc.g β 0)|
        ≤ ∑ i, |a i * (PowerArc.g β (2 * (m : ℝ) + d i + 1) / PowerArc.g β 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |a i / PowerArc.g β 0| * |PowerArc.g β (2 * (m : ℝ) + ((d i : ℝ) + 1))| := by
          apply Finset.sum_congr rfl
          intro i _
          rw [show (2 * (m : ℝ) + (d i) + 1) = 2 * (m : ℝ) + ((d i : ℝ) + 1) by ring,
            ← abs_mul]
          congr 1
          ring
  have hbound := (hfam (4323618/10000000 : ℝ) hb hb1
      (fun i : Fin 12 => shift (familyIndexA i))
      (fun i : Fin 12 => (coefficient (familyIndexA i)).re)).add
    (hfam (5676382/10000000 : ℝ) hc hc1
      (fun i : Fin 13 => shift (familyIndexB i))
      (fun i : Fin 13 => (coefficient (familyIndexB i)).re))
  apply Summable.of_nonneg_of_le (fun m => abs_nonneg _) (fun m => ?_) hbound
  rw [convS_trial_re_eq_families]
  unfold convolutionA convolutionB
  exact abs_add_le _ _

end KsIndex.OppositeHalf
