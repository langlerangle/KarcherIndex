module

public import KsIndexLean.AlphaOuterTailPointwise
public import KsIndexLean.AlphaOuterTail
public import KsIndexLean.AlphaGroupReflectionSigns

@[expose] public section


/-! # Conditional assembly of the two-sided residual tail

The majorant `tailB` combines four compensated groups with separate positive-
and negative-side remainder constants. It is set to zero at index zero and
is nonnegative when both remainder constants are nonnegative. Reflection
identities supply the negative-side multiplier bounds from the positive ones.

For `T ≥ 1025`, the pointwise bounds and weighted-square summability imply
a bound on the residual tail outside `[-T,T]`. The multiplier caps and
remainder estimates are explicit hypotheses. `AlphaOuterTailDischarge` proves
the required summability; later modules supply the concrete constants and budget.
-/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual PowerArc OppositeHalf

/-- The sharp zero-extended tail majorant. -/
noncomputable def tailB (s Dp Dm : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 0 else
    sigP n *
      (1/10000 * |compensatedPowerArcGroup (4323618/10000000) 15 (2*s^2/Real.pi) (1+s^2) n.natAbs|
        + 491/1000 * |compensatedPowerArcGroup (4323618/10000000) 14 (2*s^2/Real.pi) (1+s^2) n.natAbs|
        + (17/20 * |compensatedPowerArcGroup (5676382/10000000) 15 (2*s^2/Real.pi) (1+s^2) n.natAbs|
          + 3/10000 * |compensatedPowerArcGroup (5676382/10000000) 14 (2*s^2/Real.pi) (1+s^2) n.natAbs|))
    + (2*s^2/Real.pi) * ((if 0 < n then Dp else Dm) / (n.natAbs : ℝ))

theorem tailB_nonneg (s Dp Dm : ℝ) (hDp : 0 ≤ Dp) (hDm : 0 ≤ Dm) (n : ℤ) :
    0 ≤ tailB s Dp Dm n := by
  unfold tailB
  by_cases h0 : n = 0
  · simp [h0]
  · rw [if_neg h0]
    have hsp : 0 < sigP n := by
      have h := residualWeight_pos n; rwa [residualWeight, if_neg h0] at h
    have hterm : 0 ≤ sigP n *
        (1/10000 * |compensatedPowerArcGroup (4323618/10000000) 15 (2*s^2/Real.pi) (1+s^2) n.natAbs|
          + 491/1000 * |compensatedPowerArcGroup (4323618/10000000) 14 (2*s^2/Real.pi) (1+s^2) n.natAbs|
          + (17/20 * |compensatedPowerArcGroup (5676382/10000000) 15 (2*s^2/Real.pi) (1+s^2) n.natAbs|
            + 3/10000 * |compensatedPowerArcGroup (5676382/10000000) 14 (2*s^2/Real.pi) (1+s^2) n.natAbs|)) := by
      apply mul_nonneg hsp.le; positivity
    have hrem : 0 ≤ (2*s^2/Real.pi) * ((if 0 < n then Dp else Dm) / (n.natAbs : ℝ)) := by
      apply mul_nonneg (by positivity)
      apply div_nonneg _ (by positivity)
      split_ifs <;> assumption
    linarith

/-- Pointwise tail bound: `|realResidual s n| ≤ tailB s Dp Dm n` for `|n| > T` (T ≥ 1025). Negative-side
caps are derived from the positive ones via the reflection lemmas. -/
theorem realResidual_le_tailB (s : ℝ) (T : ℕ) (hT : 1025 ≤ T) (Dp Dm : ℝ)
    (hrawP : ∀ m : ℕ, T < m → |rawRemainder (m : ℝ)| ≤ Dp / (m : ℝ))
    (hrawM : ∀ m : ℕ, T < m → |rawRemainderNegative (m : ℝ)| ≤ Dm / (m : ℝ))
    (hAe : ∀ m : ℕ, T < m → |trialGroupMult grpAe (4323618/10000000) 15 ((m : ℝ) + 9/2)| ≤ 1/10000)
    (hAo : ∀ m : ℕ, T < m → |trialGroupMult grpAo (4323618/10000000) 14 ((m : ℝ) + 9/2)| ≤ 491/1000)
    (hBe : ∀ m : ℕ, T < m → |trialGroupMult grpBe (5676382/10000000) 15 ((m : ℝ) + 9/2)| ≤ 17/20)
    (hBo : ∀ m : ℕ, T < m → |trialGroupMult grpBo (5676382/10000000) 14 ((m : ℝ) + 9/2)| ≤ 3/10000) :
    ∀ n : ℤ, (T : ℤ) < |n| → |realResidual s n| ≤ tailB s Dp Dm n := by
  intro n hn
  have hm : T < n.natAbs := by
    rw [← Int.natCast_natAbs] at hn; exact_mod_cast hn
  have h3 : 3 ≤ n.natAbs := by omega
  have hn0 : n ≠ 0 := by rintro rfl; simp at hm
  rcases lt_trichotomy n 0 with hneg | hz | hpos
  · have hcast : -((n.natAbs : ℤ)) = n := by
      have : ((n.natAbs : ℤ)) = -n := by rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (by omega)
      omega
    have rAe : |trialGroupMultR grpAe (4323618/10000000) 15 ((n.natAbs : ℝ) + 9/2)| ≤ 1/10000 := by
      rw [grpAe_mult_reflection, abs_neg]; exact hAe _ hm
    have rAo : |trialGroupMultR grpAo (4323618/10000000) 14 ((n.natAbs : ℝ) + 9/2)| ≤ 491/1000 := by
      rw [grpAo_mult_reflection, abs_neg]; exact hAo _ hm
    have rBe : |trialGroupMultR grpBe (5676382/10000000) 15 ((n.natAbs : ℝ) + 9/2)| ≤ 17/20 := by
      rw [grpBe_mult_reflection]; exact hBe _ hm
    have rBo : |trialGroupMultR grpBo (5676382/10000000) 14 ((n.natAbs : ℝ) + 9/2)| ≤ 3/10000 := by
      rw [grpBo_mult_reflection]; exact hBo _ hm
    have hb2 := realResidual_tail_bound_neg s n.natAbs h3 Dm (hrawM _ hm) rAe rAo rBe rBo
    rw [hcast] at hb2
    rw [tailB, if_neg hn0, if_neg (by omega : ¬ 0 < n)]
    exact hb2
  · exact absurd hz hn0
  · have hcast : ((n.natAbs : ℤ)) = n := Int.natAbs_of_nonneg (by omega)
    have hb2 := realResidual_tail_bound_pos s n.natAbs h3 Dp (hrawP _ hm)
      (hAe _ hm) (hAo _ hm) (hBe _ hm) (hBo _ hm)
    rw [hcast] at hb2
    rw [tailB, if_neg hn0, if_pos hpos]
    exact hb2

/-- Conditional outer-tail theorem: the `|n| > T` tail of the certificate's weighted residual sum is
summable and bounded by the tail of the `tailB` majorant, given the per-group caps, the `D/n` remainder
bounds, and the weighted-square summability of `tailB`. -/
theorem outer_tail_conditional (s : ℝ) (T : ℕ) (hT : 1025 ≤ T) (Dp Dm : ℝ)
    (hDp : 0 ≤ Dp) (hDm : 0 ≤ Dm)
    (hrawP : ∀ m : ℕ, T < m → |rawRemainder (m : ℝ)| ≤ Dp / (m : ℝ))
    (hrawM : ∀ m : ℕ, T < m → |rawRemainderNegative (m : ℝ)| ≤ Dm / (m : ℝ))
    (hAe : ∀ m : ℕ, T < m → |trialGroupMult grpAe (4323618/10000000) 15 ((m : ℝ) + 9/2)| ≤ 1/10000)
    (hAo : ∀ m : ℕ, T < m → |trialGroupMult grpAo (4323618/10000000) 14 ((m : ℝ) + 9/2)| ≤ 491/1000)
    (hBe : ∀ m : ℕ, T < m → |trialGroupMult grpBe (5676382/10000000) 15 ((m : ℝ) + 9/2)| ≤ 17/20)
    (hBo : ∀ m : ℕ, T < m → |trialGroupMult grpBo (5676382/10000000) 14 ((m : ℝ) + 9/2)| ≤ 3/10000)
    (hsum : Summable (fun n : ℤ => if (T : ℤ) < |n| then tailB s Dp Dm n ^ 2 / residualWeight n else 0)) :
    Summable (fun n : ℤ => if (T : ℤ) < |n| then headRealResidual s n ^ 2 / residualWeight n else 0) ∧
      (∑' n : ℤ, (if (T : ℤ) < |n| then headRealResidual s n ^ 2 / residualWeight n else 0))
        ≤ ∑' n : ℤ, (if (T : ℤ) < |n| then tailB s Dp Dm n ^ 2 / residualWeight n else 0) :=
  weighted_tail_le s T (tailB s Dp Dm) (tailB_nonneg s Dp Dm hDp hDm)
    (realResidual_le_tailB s T hT Dp Dm hrawP hrawM hAe hAo hBe hBo) hsum

end KsIndex.AlphaRemarkTrial

#print axioms KsIndex.AlphaRemarkTrial.realResidual_le_tailB
#print axioms KsIndex.AlphaRemarkTrial.outer_tail_conditional
