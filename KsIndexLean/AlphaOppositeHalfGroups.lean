module

public import KsIndexLean.AlphaMomentSplit
public import KsIndexLean.PowerArcStieltjesSplit

@[expose] public section


/-! # The opposite-half sum as Stieltjes transforms

For residual indices `n ≥ 1`, the opposite half consists of `m ≤ -1`.
Reflection through `m = -1-t` and the identity `opposite_pointwise` split its
summand into three terms involving the reflected demodulated sequence.
Summability permits the corresponding split of the infinite sum.

The result contains the sum of that sequence and two weighted sums, each
written as a four-term prefix plus a 25-term Stieltjes combination. Their
transform parameters are `n + 9/2` and `13/3`, with orders `9 - shift i`.
The coefficients remain symbolic; reduction to four base transforms and the
negative-index decomposition are separate results. -/

noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ Real PowerArc KsIndex.AlphaRemarkTrial

/-- The real part of the actual trial convolution. -/
def vTrial : ℤ → ℝ := fun m => (convS trial m).re

/-- The reflected demodulated sequence `(-1)^t · v(-1-t)`. -/
def reflectedDemod (t : ℕ) : ℝ := (-1 : ℝ) ^ t * vTrial (-1 - t)

lemma exponent_le_one (i : Fin 25) : exponent i ≤ 1 := by
  fin_cases i <;> norm_num [exponent]

lemma shift_le_six (i : Fin 25) : shift i ≤ 6 := by
  fin_cases i <;> norm_num [shift]

lemma summable_abs_vTrial : Summable (fun m : ℤ => |vTrial m|) :=
  summable_abs_convS_trial_re

lemma summable_abs_reflectedDemod : Summable (fun t : ℕ => |reflectedDemod t|) := by
  have h := summable_abs_vTrial.comp_injective
    (fun a b h => by simp only at h; omega : Function.Injective
      (fun t : ℕ => (-1 - t : ℤ)))
  apply h.congr
  intro t
  simp only [Function.comp_def, reflectedDemod, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul]

lemma summable_reflectedDemod : Summable reflectedDemod :=
  Summable.of_abs summable_abs_reflectedDemod

lemma summable_reflectedDemod_div {z : ℝ} (hz : 0 < z) :
    Summable (fun t : ℕ => reflectedDemod t / ((t : ℝ) + z)) := by
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun t => abs_nonneg _) (fun t => ?_)
    (summable_abs_reflectedDemod.mul_left (1 / z))
  have hab : (0 : ℝ) < (t : ℝ) + z := by positivity
  have h1 : z ≤ (t : ℝ) + z := by
    have := Nat.cast_nonneg (α := ℝ) t
    linarith
  rw [abs_div, abs_of_pos hab,
    show 1 / z * |reflectedDemod t| = |reflectedDemod t| / z by ring]
  gcongr

/-- The trial convolution's real part, term by term. -/
lemma vTrial_eq_sum (m : ℤ) :
    vTrial m = ∑ i : Fin 25, (coefficient i).re *
      (g (exponent i) (2 * (m : ℝ) + (shift i + 1)) / g (exponent i) 0) := by
  rw [vTrial, convS_trial]
  change Complex.reAddGroupHom (∑ i : Fin 25, coefficient i *
    (g (exponent i) (2 * (m : ℝ) + (shift i + 1)) / g (exponent i) 0 : ℝ)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (coefficient i *
    (g (exponent i) (2 * (m : ℝ) + (shift i + 1)) / g (exponent i) 0 : ℝ)).re = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The reflected sequence, term by term (`g_neg` folds the argument). -/
lemma reflectedDemod_eq_sum (t : ℕ) :
    reflectedDemod t = (-1 : ℝ) ^ t * ∑ i : Fin 25, (coefficient i).re *
      (g (exponent i) ((2 * (t : ℝ) + 1) - shift i) / g (exponent i) 0) := by
  rw [reflectedDemod, vTrial_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  rw [show (2 * ((-1 - t : ℤ) : ℝ) + ((shift i : ℝ) + 1)) =
      -((2 * (t : ℝ) + 1) - shift i) by push_cast; ring, g_neg]

lemma summable_term_stieltjes (i : Fin 25) {z : ℝ} (hz : 0 < z) :
    Summable (fun k : ℕ =>
      ((-1 : ℝ) ^ k * g (exponent i) ((9 - shift i) + 2 * k)) / ((k : ℝ) + z)) := by
  have hr : exponent i ≤ 9 - (shift i : ℝ) := by
    have h1 := exponent_le_one i
    have h2 : (shift i : ℝ) ≤ 6 := by exact_mod_cast shift_le_six i
    linarith
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    ((abs_g_summable (exponent_pos i) hr).mul_left (1 / z))
  have hab : (0 : ℝ) < (k : ℝ) + z := by positivity
  have h1 : z ≤ (k : ℝ) + z := by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hab,
    show 1 / z * |g (exponent i) ((9 - (shift i : ℝ)) + 2 * k)| =
      |g (exponent i) ((9 - (shift i : ℝ)) + 2 * k)| / z by ring]
  gcongr

/-- Uniform shifted-moment reduction: the reflected half-line sum against
`1/(t+z)` equals the `t = 0..3` prefix plus the 25-term symbolic Stieltjes
combination at `z + 4`. -/
theorem refl_shifted_tsum (z : ℝ) (hz : 0 < z) :
    (∑' t : ℕ, reflectedDemod t / ((t : ℝ) + z)) =
      (∑ t ∈ Finset.range 4, reflectedDemod t / ((t : ℝ) + z))
      + ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
          powerArcStieltjes (exponent i) (9 - shift i) (z + 4) := by
  rw [← (summable_reflectedDemod_div hz).sum_add_tsum_nat_add 4]
  congr 1
  have hterm : (fun k : ℕ => reflectedDemod (k + 4) / (((k + 4 : ℕ) : ℝ) + z)) =
      fun k : ℕ => ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
        (((-1 : ℝ) ^ k * g (exponent i) ((9 - shift i) + 2 * k)) /
          ((k : ℝ) + (z + 4))) := by
    funext k
    rw [reflectedDemod_eq_sum, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [show ((2 * ((k + 4 : ℕ) : ℝ) + 1) - (shift i : ℝ)) =
        (9 - (shift i : ℝ)) + 2 * k by push_cast; ring,
      show (((k + 4 : ℕ) : ℝ) + z) = (k : ℝ) + (z + 4) by push_cast; ring,
      pow_add]
    norm_num
    ring
  rw [hterm, Summable.tsum_finsetSum (fun i _ =>
    (summable_term_stieltjes i (by linarith : (0:ℝ) < z + 4)).mul_left _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [tsum_mul_left, powerArcStieltjes]

/-- The parity factor under the reflected-and-shifted index. -/
lemma negOne_zpow_refl (t : ℕ) (n : ℤ) :
    (-1 : ℝ) ^ ((-1 - (t : ℤ)) - n) = -((-1 : ℝ) ^ t * (-1 : ℝ) ^ n) := by
  have h0 := negOne_zpow_sub 0 (1 + (t : ℤ) + n)
  simp only [zpow_zero, one_mul, zero_sub] at h0
  rw [show (-1 - (t : ℤ)) - n = -(1 + (t : ℤ) + n) by ring, h0,
    zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0),
    zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), zpow_one, zpow_natCast]
  ring

/-- Pointwise partial-fraction split of the reflected opposite-half summand. -/
lemma opposite_pointwise (n : ℤ) (hn : 1 ≤ n) (t : ℕ) :
    sigM (-1 - t) * chat ((-1 - t) - n) * vTrial (-1 - t) =
      2 / π * (-1 : ℝ) ^ n * ((3 - sigP n / (2 * (t : ℝ) + 2 * n + 1)
        - 12 / ((6 * (n : ℝ) + 1) * (6 * t + 2))) * reflectedDemod t) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have hL : (0 : ℝ) < 6 * (n : ℝ) + 1 := by linarith
  have hX : (0 : ℝ) < 6 * (t : ℝ) + 2 := by linarith
  have hY : (0 : ℝ) < 2 * (t : ℝ) + 2 * (n : ℝ) + 1 := by linarith
  simp only [sigM, sigP, chat, reflectedDemod]
  rw [negOne_zpow_refl t n,
    show ((-1 - (t : ℤ) : ℤ) : ℝ) = -1 - (t : ℝ) by push_cast; ring,
    show ((((-1 - (t : ℤ)) - n : ℤ)) : ℝ) = -1 - (t : ℝ) - n by push_cast; ring,
    abs_of_neg (show 6 * (-1 - (t : ℝ)) + 4 < 0 by linarith),
    abs_of_pos hL]
  rw [show (6 * (-1 - (t : ℝ)) + 4) = -(6 * (t : ℝ) + 2) by ring,
    show (2 * (-1 - (t : ℝ) - n) + 1) = -(2 * (t : ℝ) + 2 * n + 1) by ring]
  field_simp
  ring

/-- For `n ≥ 1`, the opposite-half transpose sum decomposes into the
reflected demodulated sum and two weighted sums. Each weighted sum has a
four-term prefix and a symbolic Stieltjes combination, at transform parameters
`n + 9/2` and `13/3` respectively. -/
theorem opposite_half_group_decomposition (n : ℤ) (hn : 1 ≤ n) :
    (∑' m : ℤ, if (6 * n + 1) * (6 * m + 4) < 0
        then sigM m * chat (m - n) * vTrial m else 0) =
      2 / π * (-1 : ℝ) ^ n *
        (3 * (∑' t : ℕ, reflectedDemod t)
         - sigP n * (1/2) *
            ((∑ t ∈ Finset.range 4, reflectedDemod t / ((t : ℝ) + ((n : ℝ) + 1/2)))
             + ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
                 powerArcStieltjes (exponent i) (9 - shift i) (((n : ℝ) + 1/2) + 4))
         - 12 / (6 * (n : ℝ) + 1) * (1/6) *
            ((∑ t ∈ Finset.range 4, reflectedDemod t / ((t : ℝ) + 1/3))
             + ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
                 powerArcStieltjes (exponent i) (9 - shift i) ((1/3 : ℝ) + 4))) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hz1 : (0 : ℝ) < (n : ℝ) + 1/2 := by linarith
  have hz2 : (0 : ℝ) < (1/3 : ℝ) := by norm_num
  -- reindex the opposite half through m = -1 - t
  have hinj : Function.Injective (fun t : ℕ => (-1 - t : ℤ)) :=
    fun a b h => by simp only at h; omega
  have hsupp : Function.support (fun m : ℤ =>
      if (6 * n + 1) * (6 * m + 4) < 0
        then sigM m * chat (m - n) * vTrial m else 0) ⊆
      Set.range (fun t : ℕ => (-1 - t : ℤ)) := by
    intro m hm
    rcases lt_or_ge m 0 with hm2 | hm2
    · exact ⟨(-1 - m).toNat, by simp only; omega⟩
    · exfalso
      apply hm
      have h0 : ¬ (6 * n + 1) * (6 * m + 4) < 0 :=
        not_lt.mpr (le_of_lt (mul_pos
          (show (0 : ℤ) < 6 * n + 1 by omega) (show (0 : ℤ) < 6 * m + 4 by omega)))
      simp only [if_neg h0]
  rw [← Function.Injective.tsum_eq hinj hsupp]
  have hstep : (∑' t : ℕ, if (6 * n + 1) * (6 * (-1 - (t : ℤ)) + 4) < 0
      then sigM (-1 - t) * chat ((-1 - t) - n) * vTrial (-1 - t) else 0) =
      ∑' t : ℕ,
        ((2 / π * (-1 : ℝ) ^ n * 3) * reflectedDemod t
         + (-(2 / π * (-1 : ℝ) ^ n * sigP n * (1/2))) *
             (reflectedDemod t / ((t : ℝ) + ((n : ℝ) + 1/2)))
         + (-(2 / π * (-1 : ℝ) ^ n * (12 / (6 * (n : ℝ) + 1)) * (1/6))) *
             (reflectedDemod t / ((t : ℝ) + 1/3))) := by
    apply tsum_congr
    intro t
    rw [if_pos (mul_neg_of_pos_of_neg (show (0 : ℤ) < 6 * n + 1 by omega)
      (show 6 * (-1 - (t : ℤ)) + 4 < 0 by omega)),
      opposite_pointwise n hn t,
      show (2 * (t : ℝ) + 2 * (n : ℝ) + 1) = 2 * ((t : ℝ) + ((n : ℝ) + 1/2)) by ring,
      show (6 * (t : ℝ) + 2) = 6 * ((t : ℝ) + 1/3) by ring]
    have h1 : ((t : ℝ) + ((n : ℝ) + 1/2)) ≠ 0 := by positivity
    have h2 : ((t : ℝ) + (1/3 : ℝ)) ≠ 0 := by positivity
    field_simp
    ring
  have s1 := summable_reflectedDemod.mul_left (2 / π * (-1 : ℝ) ^ n * 3)
  have s2 := (summable_reflectedDemod_div hz1).mul_left
    (-(2 / π * (-1 : ℝ) ^ n * sigP n * (1/2)))
  have s3 := (summable_reflectedDemod_div hz2).mul_left
    (-(2 / π * (-1 : ℝ) ^ n * (12 / (6 * (n : ℝ) + 1)) * (1/6)))
  have hsplit : (∑' t : ℕ,
        ((2 / π * (-1 : ℝ) ^ n * 3) * reflectedDemod t
         + (-(2 / π * (-1 : ℝ) ^ n * sigP n * (1/2))) *
             (reflectedDemod t / ((t : ℝ) + ((n : ℝ) + 1/2)))
         + (-(2 / π * (-1 : ℝ) ^ n * (12 / (6 * (n : ℝ) + 1)) * (1/6))) *
             (reflectedDemod t / ((t : ℝ) + 1/3)))) =
      2 / π * (-1 : ℝ) ^ n *
        (3 * (∑' t : ℕ, reflectedDemod t)
         - sigP n * (1/2) *
            ((∑ t ∈ Finset.range 4, reflectedDemod t / ((t : ℝ) + ((n : ℝ) + 1/2)))
             + ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
                 powerArcStieltjes (exponent i) (9 - shift i) (((n : ℝ) + 1/2) + 4))
         - 12 / (6 * (n : ℝ) + 1) * (1/6) *
            ((∑ t ∈ Finset.range 4, reflectedDemod t / ((t : ℝ) + 1/3))
             + ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
                 powerArcStieltjes (exponent i) (9 - shift i) ((1/3 : ℝ) + 4))) := by
    rw [(s1.add s2).tsum_add s3, s1.tsum_add s2, tsum_mul_left, tsum_mul_left,
      tsum_mul_left, refl_shifted_tsum ((n : ℝ) + 1/2) hz1,
      refl_shifted_tsum (1/3) hz2]
    ring
  exact hstep.trans hsplit

end KsIndex.OppositeHalf
