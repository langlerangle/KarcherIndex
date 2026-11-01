module

public import KsIndexLean.AlphaOuterTailSummable

@[expose] public section


/-! # Summability of the two-sided residual majorant

The bounds `sigP n ≤ 6|n|+1` and `1 ≤ sigP n` off zero reduce the weighted
square of `tailB` to four summable group-energy terms and a reciprocal-square
remainder. This proves summability on both sides of any natural-number cutoff.

The final comparison theorem combines that summability with the pointwise
assembly. It retains the four multiplier-cap hypotheses, two side-specific
remainder bounds, nonnegative remainder constants and `T ≥ 1025`.
-/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual PowerArc OppositeHalf

private lemma six_n_add_one_ne (n : ℤ) : (6 * (n : ℝ) + 1) ≠ 0 := by
  intro h
  have h2 : ((6 * n + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
  have : (6 * n + 1 : ℤ) = 0 := by exact_mod_cast h2
  omega

/-- `sigP n ≤ 6|n|+1`. -/
lemma sigP_le (n : ℤ) : sigP n ≤ 6 * (n.natAbs : ℝ) + 1 := by
  have hpos : 0 < |6 * (n : ℝ) + 1| := abs_pos.mpr (six_n_add_one_ne n)
  have habs : |6 * (n : ℝ) + 1| ≤ 6 * (n.natAbs : ℝ) + 1 := by
    have h1 : |6 * (n : ℝ) + 1| ≤ |6 * (n : ℝ)| + 1 := by
      calc |6 * (n : ℝ) + 1| ≤ |6 * (n : ℝ)| + |(1 : ℝ)| := abs_add_le _ _
        _ = |6 * (n : ℝ)| + 1 := by norm_num
    have h2 : |6 * (n : ℝ)| = 6 * (n.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, abs_mul]; norm_num
    linarith
  rw [sigP, div_le_iff₀ hpos]
  nlinarith [habs, abs_nonneg (6 * (n : ℝ) + 1), (sq_abs (6 * (n : ℝ) + 1)).symm, hpos]

/-- `1 ≤ sigP n` for `n ≠ 0` (then `|6n+1| ≥ 5`). -/
lemma one_le_sigP (n : ℤ) (hn : n ≠ 0) : 1 ≤ sigP n := by
  exact le_trans (by norm_num : (1 : ℝ) ≤ 21 / 5)
    (CircleQ.sigP_ge_of_ne_zero hn)

lemma sigP_pos (n : ℤ) (hn : n ≠ 0) : 0 < sigP n := lt_of_lt_of_le one_pos (one_le_sigP n hn)

/-- Coarse bound: `(A·C + r)²/A ≤ 2·W·C² + 2·r²` when `1 ≤ A ≤ W`. -/
private lemma coarse_div_bound {A C W r : ℝ} (hA1 : 1 ≤ A) (hAW : A ≤ W) :
    (A * C + r) ^ 2 / A ≤ 2 * W * C ^ 2 + 2 * r ^ 2 := by
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA1
  rw [div_le_iff₀ hA0]
  nlinarith [sq_nonneg (A * C - r),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hAW) hA0.le) (sq_nonneg C),
    mul_nonneg (sub_nonneg.mpr hA1) (sq_nonneg r)]

/-- `(a+b+(c+d))² ≤ 4(a²+b²+c²+d²)`. -/
private lemma sq_sum4_le (a b c d : ℝ) : (a + b + (c + d)) ^ 2 ≤ 4 * (a^2 + b^2 + c^2 + d^2) := by
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (a-d), sq_nonneg (b-c),
    sq_nonneg (b-d), sq_nonneg (c-d)]

/-- Scaled masked group tail is summable. -/
private lemma group_masked_summable (β r κ w c : ℝ)
    (hβ : β = 4323618/10000000 ∨ β = 5676382/10000000) (hr : r = 14 ∨ r = 15) (T : ℕ) :
    Summable (fun m : ℕ =>
      if T < m then c * ((6*(m:ℝ)+1) * compensatedPowerArcGroup β r κ w m ^ 2) else 0) := by
  simpa only [mul_ite, mul_zero] using (group_weighted_tail_summable β r κ w hβ hr T).mul_left c

/-- Masked `1/m²` tail is summable (nonneg scalar). -/
private lemma rem_masked_summable {c : ℝ} (hc : 0 ≤ c) (T : ℕ) :
    Summable (fun m : ℕ => if T < m then c / (m:ℝ)^2 else 0) := by
  have hfull : Summable (fun m : ℕ => c / (m:ℝ)^2) := by
    simpa only [mul_one_div] using
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).mul_left c
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hfull
  · split_ifs with h
    · exact div_nonneg hc (by positivity)
    · exact le_rfl
  · split_ifs with h
    · exact le_rfl
    · exact div_nonneg hc (by positivity)

set_option maxHeartbeats 1000000 in
/-- Per-term bound: `tailB² / sigP` on the tail, bounded by the four `(6m+1)`-weighted group squares and
the `1/m²` remainder. -/
private lemma key_bound (s Dp Dm : ℝ) (n : ℤ) (hn : n ≠ 0) :
    tailB s Dp Dm n ^ 2 / sigP n ≤
      8*(1/10000)^2*((6*(n.natAbs:ℝ)+1)*compensatedPowerArcGroup (4323618/10000000) 15 (2*s^2/Real.pi) (1+s^2) n.natAbs ^2)
      + 8*(491/1000)^2*((6*(n.natAbs:ℝ)+1)*compensatedPowerArcGroup (4323618/10000000) 14 (2*s^2/Real.pi) (1+s^2) n.natAbs ^2)
      + 8*(17/20)^2*((6*(n.natAbs:ℝ)+1)*compensatedPowerArcGroup (5676382/10000000) 15 (2*s^2/Real.pi) (1+s^2) n.natAbs ^2)
      + 8*(3/10000)^2*((6*(n.natAbs:ℝ)+1)*compensatedPowerArcGroup (5676382/10000000) 14 (2*s^2/Real.pi) (1+s^2) n.natAbs ^2)
      + 2*(2*s^2/Real.pi)^2*(if 0<n then Dp else Dm)^2/(n.natAbs:ℝ)^2 := by
  have hs1 := one_le_sigP n hn
  have hsle := sigP_le n
  rw [tailB, if_neg hn]
  set cAe := compensatedPowerArcGroup (4323618/10000000) 15 (2*s^2/Real.pi) (1+s^2) n.natAbs with hcAe
  set cAo := compensatedPowerArcGroup (4323618/10000000) 14 (2*s^2/Real.pi) (1+s^2) n.natAbs with hcAo
  set cBe := compensatedPowerArcGroup (5676382/10000000) 15 (2*s^2/Real.pi) (1+s^2) n.natAbs with hcBe
  set cBo := compensatedPowerArcGroup (5676382/10000000) 14 (2*s^2/Real.pi) (1+s^2) n.natAbs with hcBo
  set C := (1/10000 * |cAe| + 491/1000 * |cAo| + (17/20 * |cBe| + 3/10000 * |cBo|)) with hCdef
  set r := (2*s^2/Real.pi) * ((if 0<n then Dp else Dm) / (n.natAbs:ℝ)) with hrdef
  have hcoarse := coarse_div_bound (A := sigP n) (C := C) (W := 6*(n.natAbs:ℝ)+1) (r := r) hs1 hsle
  refine le_trans hcoarse ?_
  have hC2 : C^2 ≤ 4*((1/10000)^2*cAe^2 + (491/1000)^2*cAo^2 + (17/20)^2*cBe^2 + (3/10000)^2*cBo^2) := by
    rw [hCdef]
    nlinarith [sq_sum4_le (1/10000*|cAe|) (491/1000*|cAo|) (17/20*|cBe|) (3/10000*|cBo|),
      sq_abs cAe, sq_abs cAo, sq_abs cBe, sq_abs cBo]
  have hw : (0:ℝ) ≤ 6*(n.natAbs:ℝ)+1 := by positivity
  have hr2 : 2*r^2 = 2*(2*s^2/Real.pi)^2*(if 0<n then Dp else Dm)^2/(n.natAbs:ℝ)^2 := by
    rw [hrdef, div_pow, mul_pow]; ring
  rw [hr2]
  have hgroups : 2*(6*(n.natAbs:ℝ)+1)*C^2 ≤
      8*(1/10000)^2*((6*(n.natAbs:ℝ)+1)*cAe^2) + 8*(491/1000)^2*((6*(n.natAbs:ℝ)+1)*cAo^2)
      + 8*(17/20)^2*((6*(n.natAbs:ℝ)+1)*cBe^2) + 8*(3/10000)^2*((6*(n.natAbs:ℝ)+1)*cBo^2) := by
    nlinarith [mul_nonneg hw (sub_nonneg.mpr hC2), hw]
  linarith [hgroups]

/-- The side-specific tail majorant (5 masked summable pieces). -/
private def Maj (s : ℝ) (T : ℕ) (D : ℝ) (m : ℕ) : ℝ :=
    (if T < m then 8*(1/10000)^2*((6*(m:ℝ)+1)*compensatedPowerArcGroup (4323618/10000000) 15 (2*s^2/Real.pi) (1+s^2) m ^2) else 0)
  + (if T < m then 8*(491/1000)^2*((6*(m:ℝ)+1)*compensatedPowerArcGroup (4323618/10000000) 14 (2*s^2/Real.pi) (1+s^2) m ^2) else 0)
  + (if T < m then 8*(17/20)^2*((6*(m:ℝ)+1)*compensatedPowerArcGroup (5676382/10000000) 15 (2*s^2/Real.pi) (1+s^2) m ^2) else 0)
  + (if T < m then 8*(3/10000)^2*((6*(m:ℝ)+1)*compensatedPowerArcGroup (5676382/10000000) 14 (2*s^2/Real.pi) (1+s^2) m ^2) else 0)
  + (if T < m then 2*(2*s^2/Real.pi)^2*D^2/(m:ℝ)^2 else 0)

private lemma Maj_summable (s : ℝ) (T : ℕ) {D : ℝ} (hD : 0 ≤ D) : Summable (Maj s T D) := by
  unfold Maj
  refine ((((group_masked_summable (4323618/10000000) 15 (2*s^2/Real.pi) (1+s^2) (8*(1/10000)^2)
        (Or.inl rfl) (Or.inr rfl) T).add
      (group_masked_summable (4323618/10000000) 14 (2*s^2/Real.pi) (1+s^2) (8*(491/1000)^2)
        (Or.inl rfl) (Or.inl rfl) T)).add
      (group_masked_summable (5676382/10000000) 15 (2*s^2/Real.pi) (1+s^2) (8*(17/20)^2)
        (Or.inr rfl) (Or.inr rfl) T)).add
      (group_masked_summable (5676382/10000000) 14 (2*s^2/Real.pi) (1+s^2) (8*(3/10000)^2)
        (Or.inr rfl) (Or.inl rfl) T)).add
      (rem_masked_summable (show (0:ℝ) ≤ 2*(2*s^2/Real.pi)^2*D^2 by positivity) T)

set_option maxHeartbeats 800000 in
/-- The `|n|>T` tail of the `tailB` weighted square sum is summable, removing
`outer_tail_conditional`'s summability hypothesis. -/
theorem outer_tail_summable (s : ℝ) (T : ℕ) (Dp Dm : ℝ) (hDp : 0 ≤ Dp) (hDm : 0 ≤ Dm) :
    Summable (fun n : ℤ => if (T:ℤ) < |n| then tailB s Dp Dm n ^ 2 / residualWeight n else 0) := by
  apply Summable.of_nat_of_neg
  · refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (Maj_summable s T hDp)
    · split_ifs with h
      · exact div_nonneg (sq_nonneg _) (residualWeight_pos _).le
      · exact le_rfl
    · rw [abs_of_nonneg (Int.natCast_nonneg m)]
      split_ifs with h
      · have hm : T < m := by exact_mod_cast h
        have hne : (m : ℤ) ≠ 0 := by omega
        have hk := key_bound s Dp Dm (m : ℤ) hne
        rw [Int.natAbs_natCast] at hk
        rw [if_pos (by exact_mod_cast (by omega : 0 < m) : (0:ℤ) < (m:ℤ))] at hk
        rw [residualWeight, if_neg hne]
        rw [Maj, if_pos hm, if_pos hm, if_pos hm, if_pos hm, if_pos hm]
        linarith [hk]
      · have hmn : ¬ T < m := by exact_mod_cast h
        simp [Maj, if_neg hmn]
  · refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (Maj_summable s T hDm)
    · split_ifs with h
      · exact div_nonneg (sq_nonneg _) (residualWeight_pos _).le
      · exact le_rfl
    · rw [abs_neg, abs_of_nonneg (Int.natCast_nonneg m)]
      split_ifs with h
      · have hm : T < m := by exact_mod_cast h
        have hne : -(m : ℤ) ≠ 0 := by omega
        have hk := key_bound s Dp Dm (-(m : ℤ)) hne
        rw [Int.natAbs_neg, Int.natAbs_natCast] at hk
        rw [if_neg (by omega : ¬ (0:ℤ) < -(m:ℤ))] at hk
        rw [residualWeight, if_neg hne]
        rw [Maj, if_pos hm, if_pos hm, if_pos hm, if_pos hm, if_pos hm]
        linarith [hk]
      · have hmn : ¬ T < m := by exact_mod_cast h
        simp [Maj, if_neg hmn]

/-- Residual-tail comparison with summability supplied by `outer_tail_summable`.
The cutoff, sign, multiplier-cap and remainder hypotheses are retained. -/
theorem outer_tail_bound (s : ℝ) (T : ℕ) (hT : 1025 ≤ T) (Dp Dm : ℝ)
    (hDp : 0 ≤ Dp) (hDm : 0 ≤ Dm)
    (hrawP : ∀ m : ℕ, T < m → |rawRemainder (m : ℝ)| ≤ Dp / (m : ℝ))
    (hrawM : ∀ m : ℕ, T < m → |rawRemainderNegative (m : ℝ)| ≤ Dm / (m : ℝ))
    (hAe : ∀ m : ℕ, T < m → |trialGroupMult grpAe (4323618/10000000) 15 ((m : ℝ) + 9/2)| ≤ 1/10000)
    (hAo : ∀ m : ℕ, T < m → |trialGroupMult grpAo (4323618/10000000) 14 ((m : ℝ) + 9/2)| ≤ 491/1000)
    (hBe : ∀ m : ℕ, T < m → |trialGroupMult grpBe (5676382/10000000) 15 ((m : ℝ) + 9/2)| ≤ 17/20)
    (hBo : ∀ m : ℕ, T < m → |trialGroupMult grpBo (5676382/10000000) 14 ((m : ℝ) + 9/2)| ≤ 3/10000) :
    Summable (fun n : ℤ => if (T : ℤ) < |n| then headRealResidual s n ^ 2 / residualWeight n else 0) ∧
      (∑' n : ℤ, (if (T : ℤ) < |n| then headRealResidual s n ^ 2 / residualWeight n else 0))
        ≤ ∑' n : ℤ, (if (T : ℤ) < |n| then tailB s Dp Dm n ^ 2 / residualWeight n else 0) :=
  outer_tail_conditional s T hT Dp Dm hDp hDm hrawP hrawM hAe hAo hBe hBo
    (outer_tail_summable s T Dp Dm hDp hDm)

end KsIndex.AlphaRemarkTrial

#print axioms KsIndex.AlphaRemarkTrial.key_bound
#print axioms KsIndex.AlphaRemarkTrial.outer_tail_summable
#print axioms KsIndex.AlphaRemarkTrial.outer_tail_bound
