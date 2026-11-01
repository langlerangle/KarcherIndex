module

public import KsIndexLean.AlphaGroupAnchorBounds

@[expose] public section


/-! A concrete sufficient residual budget for the target lower endpoint. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual PowerArc

theorem trial_kappa_sq_le_one :
    (2*AlphaRemark.spectralUpper^2/Real.pi)^2 ≤ 1 := by
  have h := abs_le.mp trial_kappa_interval
  have hlo : -(1:ℝ) ≤ 2*AlphaRemark.spectralUpper^2/Real.pi := by
    dsimp [AlphaRemark.spectralUpper]
    linarith
  have hhi : 2*AlphaRemark.spectralUpper^2/Real.pi ≤ 1 := by
    dsimp [AlphaRemark.spectralUpper]
    linarith
  nlinarith

/-- Unit raw-remainder constants suffice at the outer cutoff 2048. -/
theorem concrete_scalar_tail_budget :
    2*(1+(1:ℝ))*(∑ i : Fin 4, tailGroupCap i*anchorGroupU i)^2 +
      (1+1/(1:ℝ))*(2*AlphaRemark.spectralUpper^2/Real.pi)^2*
        ((1:ℝ)^2+1^2)/(10*(2048:ℝ)^2) ≤ 1/2000000 := by
  have hk := trial_kappa_sq_le_one
  norm_num [Fin.sum_univ_succ, tailGroupCap, anchorGroupU] at ⊢
  nlinarith

/-- The phase lower bound follows from a finite-window certificate, bounds on both
raw remainders, and a trial-energy lower bound. The group-energy estimate is supplied
by the anchor bounds. -/
theorem alphaStar_lower_of_concrete_window
    (a e : ℤ → ℝ)
    (hrawP : ∀ m : ℕ, 2048 < m → |rawRemainder (m:ℝ)| ≤ 1/(m:ℝ))
    (hrawM : ∀ m : ℕ, 2048 < m → |rawRemainderNegative (m:ℝ)| ≤ 1/(m:ℝ))
    (happrox : ∀ n ∈ residualWindow 2048, |windowApproximation n-a n| ≤ e n)
    (hwindow : (∑ n ∈ residualWindow 2048,
      (|a n|+e n+windowApproximationError n)^2/residualWeight n) ≤ (9/10000000 : ℝ))
    (henergy : (1628/1000000000 : ℝ) ≤ Qform AlphaRemark.spectralUpper trial) :
    (4323617/10000000 : ℝ) < Staircase.alphaStar := by
  apply alphaStar_lower_of_anchored_tail 1023 2048
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    a e (9/10000000) 1 1 1 anchorGroupU
    (by norm_num) (by norm_num) (by norm_num) anchorGroupU_pos
    hrawP hrawM anchorGroupEnergy_bound happrox hwindow ?_ henergy
  have h := concrete_scalar_tail_budget
  linarith

/-- Unit raw-remainder constants suffice at the outer cutoff 1025. -/
theorem concrete_scalar_tail_budget1025 :
    2*(1+(1:ℝ))*(∑ i : Fin 4, tailGroupCap i*anchorGroupU i)^2 +
      (1+1/(1:ℝ))*(2*AlphaRemark.spectralUpper^2/Real.pi)^2*
        ((1:ℝ)^2+1^2)/(10*(1025:ℝ)^2) ≤ 7/10000000 := by
  have hk := trial_kappa_sq_le_one
  norm_num [Fin.sum_univ_succ, tailGroupCap, anchorGroupU] at ⊢
  nlinarith

/-- The phase lower bound follows from a finite-window certificate, bounds on both
raw remainders, and a trial-energy lower bound. The group-energy estimate is supplied
by the anchor bounds. -/
theorem alphaStar_lower_of_concrete_window1025
    (a e : ℤ → ℝ)
    (hrawP : ∀ m : ℕ, 1025 < m → |rawRemainder (m:ℝ)| ≤ 1/(m:ℝ))
    (hrawM : ∀ m : ℕ, 1025 < m → |rawRemainderNegative (m:ℝ)| ≤ 1/(m:ℝ))
    (happrox : ∀ n ∈ residualWindow 1025, |windowApproximation n-a n| ≤ e n)
    (hwindow : (∑ n ∈ residualWindow 1025,
      (|a n|+e n+windowApproximationError n)^2/residualWeight n) ≤ (7/10000000 : ℝ))
    (henergy : (1628/1000000000 : ℝ) ≤ Qform AlphaRemark.spectralUpper trial) :
    (4323617/10000000 : ℝ) < Staircase.alphaStar := by
  apply alphaStar_lower_of_anchored_tail 1023 1025
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    a e (7/10000000) 1 1 1 anchorGroupU
    (by norm_num) (by norm_num) (by norm_num) anchorGroupU_pos
    hrawP hrawM anchorGroupEnergy_bound happrox hwindow ?_ henergy
  have h := concrete_scalar_tail_budget1025
  linarith

/-- A certificate for the actual residual window can use any exact representation
of its terms, including compensated-group recurrences. -/
theorem alphaStar_lower_of_actual_window1025
    (hrawP : ∀ m : ℕ, 1025 < m → |rawRemainder (m:ℝ)| ≤ 1/(m:ℝ))
    (hrawM : ∀ m : ℕ, 1025 < m → |rawRemainderNegative (m:ℝ)| ≤ 1/(m:ℝ))
    (hwindow : (∑ n ∈ residualWindow 1025,
      realResidual AlphaRemark.spectralUpper n^2/residualWeight n) ≤ (7/10000000 : ℝ))
    (henergy : (1628/1000000000 : ℝ) ≤ Qform AlphaRemark.spectralUpper trial) :
    (4323617/10000000 : ℝ) < Staircase.alphaStar := by
  have ht := outer_tail_bound_final AlphaRemark.spectralUpper 1025 (by norm_num)
    1 1 (by norm_num) (by norm_num) hrawP hrawM
  have hb := outer_tail_scalar_budget_from_anchor AlphaRemark.spectralUpper 1 1 1
    1023 1025 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    anchorGroupU anchorGroupU_pos anchorGroupEnergy_bound
  have htail := ht.2.trans (hb.trans concrete_scalar_tail_budget1025)
  have hs := residual_window_tail_sum AlphaRemark.spectralUpper 1025 ht.1
  apply alphaStar_lower_of_residual_budget hs.1 _ henergy
  rw [hs.2]
  have hh := add_le_add hwindow htail
  linarith

end KsIndex.AlphaRemarkTrial
