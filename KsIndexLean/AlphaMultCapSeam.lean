module

public import KsIndexLean.AlphaOuterTailDischarge
public import KsIndexLean.AlphaMultIdentity

@[expose] public section


/-! # Multiplier caps for the residual tail

The four identities `trialGroupMult grp_g β_g r_g (n+9/2) = M_g (2n)`
identify the finite multiplier formulas. The bounds on `M_g` give absolute caps
for `n ≥ 1026`. Specializing `outer_tail_bound` supplies these four cap hypotheses;
the cutoff and the two side-specific raw-remainder bounds remain explicit. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ PowerArc OppositeHalf AlphaResidual AlphaMultiplier

theorem trialGroupMult_grpAe_eq (n : ℝ) :
    trialGroupMult grpAe (4323618/10000000) 15 (n + 9/2) = AlphaMultIdentity.M_A0 (2*n) := by
  rw [trialGroupMult_eq_normalized, show (2*(n + 9/2) - 15 : ℝ) = 2*n - 6 by ring,
    AlphaMultIdentity.M_A0, AlphaMultIdentity.bA]
  simp [grpAe, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
    coefficient, exponent, shift, chainLen, baseShift]
  ring

theorem trialGroupMult_grpAo_eq (n : ℝ) :
    trialGroupMult grpAo (4323618/10000000) 14 (n + 9/2) = AlphaMultIdentity.M_A1 (2*n) := by
  rw [trialGroupMult_eq_normalized, show (2*(n + 9/2) - 14 : ℝ) = 2*n - 5 by ring,
    AlphaMultIdentity.M_A1, AlphaMultIdentity.bA]
  simp [grpAo, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
    coefficient, exponent, shift, chainLen, baseShift]
  ring

theorem trialGroupMult_grpBe_eq (n : ℝ) :
    trialGroupMult grpBe (5676382/10000000) 15 (n + 9/2) = AlphaMultIdentity.M_B0 (2*n) := by
  rw [trialGroupMult_eq_normalized, show (2*(n + 9/2) - 15 : ℝ) = 2*n - 6 by ring,
    AlphaMultIdentity.M_B0, AlphaMultIdentity.bB]
  simp [grpBe, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
    coefficient, exponent, shift, chainLen, baseShift]
  ring

theorem trialGroupMult_grpBo_eq (n : ℝ) :
    trialGroupMult grpBo (5676382/10000000) 14 (n + 9/2) = AlphaMultIdentity.M_B1 (2*n) := by
  rw [trialGroupMult_eq_normalized, show (2*(n + 9/2) - 14 : ℝ) = 2*n - 5 by ring,
    AlphaMultIdentity.M_B1, AlphaMultIdentity.bB]
  simp [grpBo, Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_zero,
    coefficient, exponent, shift, chainLen, baseShift]
  ring

/-! ### Absolute caps for n ≥ 1026 (from the M_g bounds at x = 2n ≥ 2051). -/

private lemma two_m_ge (m : ℕ) (hm : 1026 ≤ m) : (2051 : ℝ) ≤ 2 * (m : ℝ) := by
  have : (1026 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

theorem grpAe_cap (m : ℕ) (hm : 1026 ≤ m) :
    |trialGroupMult grpAe (4323618/10000000) 15 ((m : ℝ) + 9/2)| ≤ 1/10000 := by
  rw [trialGroupMult_grpAe_eq]
  obtain ⟨hlo, hhi⟩ := AlphaMultIdentity.M_A0_bounds (2 * (m : ℝ)) (two_m_ge m hm)
  norm_num [L_A0, U_A0] at hlo hhi
  rw [abs_le]; constructor <;> linarith

theorem grpAo_cap (m : ℕ) (hm : 1026 ≤ m) :
    |trialGroupMult grpAo (4323618/10000000) 14 ((m : ℝ) + 9/2)| ≤ 491/1000 := by
  rw [trialGroupMult_grpAo_eq]
  obtain ⟨hlo, hhi⟩ := AlphaMultIdentity.M_A1_bounds (2 * (m : ℝ)) (two_m_ge m hm)
  norm_num [L_A1, U_A1] at hlo hhi
  rw [abs_le]; constructor <;> linarith

theorem grpBe_cap (m : ℕ) (hm : 1026 ≤ m) :
    |trialGroupMult grpBe (5676382/10000000) 15 ((m : ℝ) + 9/2)| ≤ 17/20 := by
  rw [trialGroupMult_grpBe_eq]
  obtain ⟨hlo, hhi⟩ := AlphaMultIdentity.M_B0_bounds (2 * (m : ℝ)) (two_m_ge m hm)
  norm_num [L_B0, U_B0] at hlo hhi
  rw [abs_le]; constructor <;> linarith

theorem grpBo_cap (m : ℕ) (hm : 1026 ≤ m) :
    |trialGroupMult grpBo (5676382/10000000) 14 ((m : ℝ) + 9/2)| ≤ 3/10000 := by
  rw [trialGroupMult_grpBo_eq]
  obtain ⟨hlo, hhi⟩ := AlphaMultIdentity.M_B1_bounds (2 * (m : ℝ)) (two_m_ge m hm)
  norm_num [L_B1, U_B1] at hlo hhi
  rw [abs_le]; constructor <;> linarith

/-- Outer-tail comparison with the four multiplier caps supplied. The cutoff
`T ≥ 1025`, nonnegative remainder constants, and both raw-remainder bounds remain
explicit hypotheses. -/
theorem outer_tail_bound_final (s : ℝ) (T : ℕ) (hT : 1025 ≤ T) (Dp Dm : ℝ)
    (hDp : 0 ≤ Dp) (hDm : 0 ≤ Dm)
    (hrawP : ∀ m : ℕ, T < m → |rawRemainder (m : ℝ)| ≤ Dp / (m : ℝ))
    (hrawM : ∀ m : ℕ, T < m → |rawRemainderNegative (m : ℝ)| ≤ Dm / (m : ℝ)) :
    Summable (fun n : ℤ => if (T : ℤ) < |n| then headRealResidual s n ^ 2 / residualWeight n else 0) ∧
      (∑' n : ℤ, (if (T : ℤ) < |n| then headRealResidual s n ^ 2 / residualWeight n else 0))
        ≤ ∑' n : ℤ, (if (T : ℤ) < |n| then tailB s Dp Dm n ^ 2 / residualWeight n else 0) :=
  outer_tail_bound s T hT Dp Dm hDp hDm hrawP hrawM
    (fun m hm => grpAe_cap m (by omega)) (fun m hm => grpAo_cap m (by omega))
    (fun m hm => grpBe_cap m (by omega)) (fun m hm => grpBo_cap m (by omega))

end KsIndex.AlphaRemarkTrial

#print axioms KsIndex.AlphaRemarkTrial.trialGroupMult_grpAe_eq
#print axioms KsIndex.AlphaRemarkTrial.trialGroupMult_grpBo_eq
#print axioms KsIndex.AlphaRemarkTrial.grpAe_cap
#print axioms KsIndex.AlphaRemarkTrial.outer_tail_bound_final
