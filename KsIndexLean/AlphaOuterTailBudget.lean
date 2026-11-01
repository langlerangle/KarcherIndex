module

public import KsIndexLean.AlphaTailBudget
public import KsIndexLean.AlphaMultCapSeam

@[expose] public section


/-! Explicit scalar budgets for the concrete two-sided residual majorant. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual PowerArc

/-- Multiplier bounds for the four power-arc groups. -/
def tailGroupCap : Fin 4 → ℝ := ![1/10000, 491/1000, 17/20, 3/10000]

def tailGroupExponent : Fin 4 → ℝ :=
  ![4323618/10000000, 4323618/10000000, 5676382/10000000, 5676382/10000000]

def tailGroupEndpoint : Fin 4 → ℝ := ![15, 14, 15, 14]

def tailGroupValue (s : ℝ) (i : Fin 4) (m : ℕ) : ℝ :=
  compensatedPowerArcGroup (tailGroupExponent i) (tailGroupEndpoint i)
    (2*s^2/Real.pi) (1+s^2) m

/-- Absolute group envelope, before multiplication by the residual weight. -/
def tailGroupEnvelope (s : ℝ) (m : ℕ) : ℝ :=
  ∑ i : Fin 4, tailGroupCap i * |tailGroupValue s i m|

theorem tailGroupEnvelope_explicit (s : ℝ) (m : ℕ) :
    tailGroupEnvelope s m =
      1/10000*|compensatedPowerArcGroup (4323618/10000000) 15 (2*s^2/Real.pi) (1+s^2) m|+
      491/1000*|compensatedPowerArcGroup (4323618/10000000) 14 (2*s^2/Real.pi) (1+s^2) m|+
      (17/20*|compensatedPowerArcGroup (5676382/10000000) 15 (2*s^2/Real.pi) (1+s^2) m|+
      3/10000*|compensatedPowerArcGroup (5676382/10000000) 14 (2*s^2/Real.pi) (1+s^2) m|) := by
  simp [tailGroupEnvelope, tailGroupValue, tailGroupCap, tailGroupExponent,
    tailGroupEndpoint, Fin.sum_univ_succ]
  ring

/-- Positive-index form of the concrete majorant. -/
theorem tailB_nat (s Dp Dm : ℝ) (m : ℕ) (hm : 0 < m) :
    tailB s Dp Dm (m:ℤ) = sigP (m:ℤ)*tailGroupEnvelope s m+(2*s^2/Real.pi)*(Dp/(m:ℝ)) := by
  rw [tailB, ite_eq_right (by exact_mod_cast (Nat.ne_of_gt hm)),
    ite_eq_left (by exact_mod_cast hm), Int.natAbs_natCast, tailGroupEnvelope_explicit]

/-- Negative-index form of the concrete majorant. -/
theorem tailB_neg (s Dp Dm : ℝ) (m : ℕ) (hm : 0 < m) :
    tailB s Dp Dm (-(m:ℤ)) = sigP (-(m:ℤ))*tailGroupEnvelope s m+(2*s^2/Real.pi)*(Dm/(m:ℝ)) := by
  rw [tailB, ite_eq_right (by exact_mod_cast (show -(m:ℤ) ≠ 0 by omega)),
    ite_eq_right (by omega : ¬ 0 < -(m:ℤ)), Int.natAbs_neg, Int.natAbs_natCast,
    tailGroupEnvelope_explicit]

/-- Four individual energy bounds combine with their actual multiplier caps. -/
theorem tailGroupEnvelope_energy_from_anchor (s : ℝ) (J N : ℕ)
    (hJ : 1023 ≤ J) (hJN : J ≤ N) (u : Fin 4 → ℝ)
    (hu : ∀ i, 0 < u i)
    (henergy : ∀ i, compensatedTailEnergy (tailGroupExponent i) (tailGroupEndpoint i)
      (2*s^2/Real.pi) (1+s^2) J ≤ u i^2) :
    Summable (fun m : ℕ => if N < m then (6*(m:ℝ)+1)*tailGroupEnvelope s m^2 else 0) ∧
      (∑' m : ℕ, if N < m then (6*(m:ℝ)+1)*tailGroupEnvelope s m^2 else 0) ≤
        (∑ i : Fin 4, tailGroupCap i*u i)^2 := by
  have hg (i : Fin 4) := compensated_group_tail_mono (tailGroupExponent i) (tailGroupEndpoint i)
    (2*s^2/Real.pi) (1+s^2) J N
    (by fin_cases i <;> norm_num [tailGroupExponent])
    (by fin_cases i <;> norm_num [tailGroupEndpoint]) hJ hJN
  have h := group_energy_bound Finset.univ tailGroupCap u (tailGroupValue s)
    (fun m => if N < m then 6*(m:ℝ)+1 else 0)
    (by intro i hi; fin_cases i <;> norm_num [tailGroupCap]) (by intro i hi; exact hu i)
    (by intro m; split_ifs <;> positivity)
    (by intro i hi; simpa only [tailGroupValue, ite_mul, zero_mul] using (hg i).1)
    (by intro i hi; simpa only [tailGroupValue, ite_mul, zero_mul] using (hg i).2.trans (henergy i))
  simpa only [tailGroupEnvelope, ite_mul, zero_mul] using h

/-- Energy specialization with the anchor at the cutoff `N`; the sum runs over `m > N`. -/
theorem tailGroupEnvelope_energy (s : ℝ) (N : ℕ) (hN : 1023 ≤ N) (u : Fin 4 → ℝ)
    (hu : ∀ i, 0 < u i)
    (henergy : ∀ i, compensatedTailEnergy (tailGroupExponent i) (tailGroupEndpoint i)
      (2*s^2/Real.pi) (1+s^2) N ≤ u i^2) :
    Summable (fun m : ℕ => if N < m then (6*(m:ℝ)+1)*tailGroupEnvelope s m^2 else 0) ∧
      (∑' m : ℕ, if N < m then (6*(m:ℝ)+1)*tailGroupEnvelope s m^2 else 0) ≤
        (∑ i : Fin 4, tailGroupCap i*u i)^2 :=
  tailGroupEnvelope_energy_from_anchor s N N hN le_rfl u hu henergy

/-- The two-sided majorant budget, with a tunable separation parameter. -/
theorem outer_tail_scalar_budget_from_anchor (s Dp Dm η : ℝ) (J N : ℕ)
    (hJ : 1023 ≤ J) (hJN : J ≤ N) (hN : 1025 ≤ N)
    (hη : 0 < η) (u : Fin 4 → ℝ) (hu : ∀ i, 0 < u i)
    (henergy : ∀ i, compensatedTailEnergy (tailGroupExponent i) (tailGroupEndpoint i)
      (2*s^2/Real.pi) (1+s^2) J ≤ u i^2) :
    (∑' n : ℤ, if (N:ℤ) < |n| then tailB s Dp Dm n^2/residualWeight n else 0) ≤
      2*(1+η)*(∑ i : Fin 4, tailGroupCap i*u i)^2+
        (1+1/η)*(2*s^2/Real.pi)^2*(Dp^2+Dm^2)/(10*(N:ℝ)^2) := by
  have hg := tailGroupEnvelope_energy_from_anchor s J N hJ hJN u hu henergy
  have hp := one_side_tail_budget N (by omega) (tailGroupEnvelope s)
    (fun m => sigP (m:ℤ)) (2*s^2/Real.pi) Dp _ η hη
    (by intro m hm; exact five_mul_le_sigP_nat m (by omega))
    (by intro m hm; simpa only [Int.natAbs_natCast] using sigP_le (m:ℤ)) hg.1 hg.2
  have hm := one_side_tail_budget N (by omega) (tailGroupEnvelope s)
    (fun m => sigP (-(m:ℤ))) (2*s^2/Real.pi) Dm _ η hη
    (by intro m hm; exact five_mul_le_sigP_neg m (by omega))
    (by intro m hm; simpa only [Int.natAbs_neg, Int.natAbs_natCast] using sigP_le (-(m:ℤ))) hg.1 hg.2
  let f : ℤ → ℝ := fun n => if (N:ℤ) < |n| then tailB s Dp Dm n^2/residualWeight n else 0
  have hpos : (fun m : ℕ => f (m:ℤ)) = (fun m : ℕ => if N < m then
      (sigP (m:ℤ)*tailGroupEnvelope s m+(2*s^2/Real.pi)*(Dp/(m:ℝ)))^2/sigP (m:ℤ) else 0) := by
    funext m
    have hiff : (N:ℤ) < |(m:ℤ)| ↔ N < m := by simp
    by_cases hm0 : N < m
    · have hn0 : (m:ℤ) ≠ 0 := by omega
      simp only [f, hiff, ite_eq_left hm0, tailB_nat s Dp Dm m (by omega), residualWeight,
        ite_eq_right hn0]
    · simp only [f, hiff, ite_eq_right hm0]
  have hneg : (fun m : ℕ => f (-(m:ℤ))) = (fun m : ℕ => if N < m then
      (sigP (-(m:ℤ))*tailGroupEnvelope s m+(2*s^2/Real.pi)*(Dm/(m:ℝ)))^2/sigP (-(m:ℤ)) else 0) := by
    funext m
    have hiff : (N:ℤ) < |-(m:ℤ)| ↔ N < m := by simp
    by_cases hm0 : N < m
    · have hn0 : -(m:ℤ) ≠ 0 := by omega
      simp only [f, hiff, ite_eq_left hm0, tailB_neg s Dp Dm m (by omega), residualWeight,
        ite_eq_right hn0]
    · simp only [f, hiff, ite_eq_right hm0]
  have hps : Summable (fun m : ℕ => f (m:ℤ)) := by rw [hpos]; exact hp.1
  have hms : Summable (fun m : ℕ => f (-(m:ℤ))) := by rw [hneg]; exact hm.1
  change (∑' n, f n) ≤ _
  rw [hps.tsum_of_nat_of_neg hms, hpos, hneg]
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0, sub_zero]
  calc
    _ ≤ ((1+η)*(∑ i : Fin 4, tailGroupCap i*u i)^2+(1+1/η)*(2*s^2/Real.pi)^2*Dp^2/(10*(N:ℝ)^2))+
        ((1+η)*(∑ i : Fin 4, tailGroupCap i*u i)^2+(1+1/η)*(2*s^2/Real.pi)^2*Dm^2/(10*(N:ℝ)^2)) :=
      add_le_add hp.2 hm.2
    _ = _ := by ring

/-- Scalar budget specialization with anchor `N`; the tail contains indices `|n| > N`. -/
theorem outer_tail_scalar_budget (s Dp Dm η : ℝ) (N : ℕ) (hN : 1025 ≤ N)
    (hη : 0 < η) (u : Fin 4 → ℝ) (hu : ∀ i, 0 < u i)
    (henergy : ∀ i, compensatedTailEnergy (tailGroupExponent i) (tailGroupEndpoint i)
      (2*s^2/Real.pi) (1+s^2) N ≤ u i^2) :
    (∑' n : ℤ, if (N:ℤ) < |n| then tailB s Dp Dm n^2/residualWeight n else 0) ≤
      2*(1+η)*(∑ i : Fin 4, tailGroupCap i*u i)^2+
        (1+1/η)*(2*s^2/Real.pi)^2*(Dp^2+Dm^2)/(10*(N:ℝ)^2) :=
  outer_tail_scalar_budget_from_anchor s Dp Dm η N N (by omega) le_rfl hN hη u hu henergy

/-- The decimal lower bound from finite numerical certificates and scalar tail inputs. -/
theorem alphaStar_lower_of_scalar_tail (N : ℕ) (hN : 1025 ≤ N) (hNhi : N ≤ 16385)
    (a e : ℤ → ℝ) (W Dp Dm η : ℝ) (u : Fin 4 → ℝ)
    (hDp : 0 ≤ Dp) (hDm : 0 ≤ Dm) (hη : 0 < η) (hu : ∀ i, 0 < u i)
    (hrawP : ∀ m : ℕ, N < m → |rawRemainder (m:ℝ)| ≤ Dp/(m:ℝ))
    (hrawM : ∀ m : ℕ, N < m → |rawRemainderNegative (m:ℝ)| ≤ Dm/(m:ℝ))
    (hgroup : ∀ i, compensatedTailEnergy (tailGroupExponent i) (tailGroupEndpoint i)
      (2*AlphaRemark.spectralUpper^2/Real.pi) (1+AlphaRemark.spectralUpper^2) N ≤ u i^2)
    (happrox : ∀ n ∈ residualWindow N, |windowApproximation n-a n| ≤ e n)
    (hwindow : (∑ n ∈ residualWindow N,
      (|a n|+e n+windowApproximationError n)^2/residualWeight n) ≤ W)
    (hbudget : W+ (2*(1+η)*(∑ i : Fin 4, tailGroupCap i*u i)^2+
      (1+1/η)*(2*AlphaRemark.spectralUpper^2/Real.pi)^2*(Dp^2+Dm^2)/(10*(N:ℝ)^2)) <
      (1628/1000000000 : ℝ))
    (henergy : (1628/1000000000 : ℝ) ≤ Qform AlphaRemark.spectralUpper trial) :
    (4323617/10000000 : ℝ) < Staircase.alphaStar := by
  have ht := outer_tail_bound_final AlphaRemark.spectralUpper N hN Dp Dm hDp hDm hrawP hrawM
  have hb := outer_tail_scalar_budget AlphaRemark.spectralUpper Dp Dm η N hN hη u hu hgroup
  exact alphaStar_lower_of_window_tail N a e W _ (residualWindow_cut hNhi)
    happrox hwindow ht.1 (ht.2.trans hb) hbudget henergy

/-- Reuse an earlier certified group anchor in the final numerical budget. -/
theorem alphaStar_lower_of_anchored_tail (J N : ℕ) (hJ : 1023 ≤ J)
    (hJN : J ≤ N) (hN : 1025 ≤ N) (hNhi : N ≤ 16385)
    (a e : ℤ → ℝ) (W Dp Dm η : ℝ) (u : Fin 4 → ℝ)
    (hDp : 0 ≤ Dp) (hDm : 0 ≤ Dm) (hη : 0 < η) (hu : ∀ i, 0 < u i)
    (hrawP : ∀ m : ℕ, N < m → |rawRemainder (m:ℝ)| ≤ Dp/(m:ℝ))
    (hrawM : ∀ m : ℕ, N < m → |rawRemainderNegative (m:ℝ)| ≤ Dm/(m:ℝ))
    (hgroup : ∀ i, compensatedTailEnergy (tailGroupExponent i) (tailGroupEndpoint i)
      (2*AlphaRemark.spectralUpper^2/Real.pi) (1+AlphaRemark.spectralUpper^2) J ≤ u i^2)
    (happrox : ∀ n ∈ residualWindow N, |windowApproximation n-a n| ≤ e n)
    (hwindow : (∑ n ∈ residualWindow N,
      (|a n|+e n+windowApproximationError n)^2/residualWeight n) ≤ W)
    (hbudget : W+ (2*(1+η)*(∑ i : Fin 4, tailGroupCap i*u i)^2+
      (1+1/η)*(2*AlphaRemark.spectralUpper^2/Real.pi)^2*(Dp^2+Dm^2)/(10*(N:ℝ)^2)) <
      (1628/1000000000 : ℝ))
    (henergy : (1628/1000000000 : ℝ) ≤ Qform AlphaRemark.spectralUpper trial) :
    (4323617/10000000 : ℝ) < Staircase.alphaStar := by
  have ht := outer_tail_bound_final AlphaRemark.spectralUpper N hN Dp Dm hDp hDm hrawP hrawM
  have hb := outer_tail_scalar_budget_from_anchor AlphaRemark.spectralUpper Dp Dm η J N hJ hJN hN hη u hu hgroup
  exact alphaStar_lower_of_window_tail N a e W _ (residualWindow_cut hNhi)
    happrox hwindow ht.1 (ht.2.trans hb) hbudget henergy

end KsIndex.AlphaRemarkTrial
