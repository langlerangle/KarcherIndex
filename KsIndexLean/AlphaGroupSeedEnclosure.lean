module

public import KsIndexLean.AlphaCompensatedGroupEnergy
public import KsIndexLean.AlphaStieltjesFullSeedIntervals
public import KsIndexLean.AlphaOuterCoefficientSeeds

@[expose] public section


/-! Scalar interval assembly for the initial compensated power-arc groups. -/
namespace KsIndex.PowerArc

theorem affine_group_abs_bound (w κ κ₀ T u u₀ H H₀ a a₀ du dH da dk R : ℝ)
    (hu : |u-u₀| ≤ du) (hH : |H-H₀| ≤ dH) (ha : |a-a₀| ≤ da)
    (hk : |κ-κ₀| ≤ dk) (hdy : 0 ≤ dH + |T| *da)
    (hbudget : |w| *du + (|κ₀|+dk)*(dH+|T| *da) + dk*|-H₀+T*a₀| +
      |w*u₀+κ₀*(-H₀+T*a₀)| ≤ R) : |w*u+κ*(-H+T*a)| ≤ R := by
  have hy : |(-H+T*a)-(-H₀+T*a₀)| ≤ dH+|T| *da := by
    calc
      _ = |-(H-H₀)+T*(a-a₀)| := by congr 1; ring
      _ ≤ |-(H-H₀)|+|T*(a-a₀)| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_neg, abs_mul]
        exact add_le_add hH (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
  have hp : |κ*(-H+T*a)-κ₀*(-H₀+T*a₀)| ≤
      (|κ₀|+dk)*(dH+|T| *da)+dk*|-H₀+T*a₀| := by
    apply scalar_enclosure_transfer _ κ κ₀ (-H₀+T*a₀) (dH+|T| *da) dk _ _
    · rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    · exact hk
    · exact hdy
    · simp only [sub_self, abs_zero, add_zero, le_refl]
  have hu' : |w*u-w*u₀| ≤ |w| *du := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)
  calc
    _ ≤ |w*u-w*u₀|+|κ*(-H+T*a)-κ₀*(-H₀+T*a₀)|+
        |w*u₀+κ₀*(-H₀+T*a₀)| := by
      have hh := abs_add_le (w*u-w*u₀) (κ*(-H+T*a)-κ₀*(-H₀+T*a₀))
      have hh' := abs_sub_le (w*u+κ*(-H+T*a)) (w*u₀+κ₀*(-H₀+T*a₀)) 0
      rw [show (w*u-w*u₀)+(κ*(-H+T*a)-κ₀*(-H₀+T*a₀)) =
        (w*u+κ*(-H+T*a))-(w*u₀+κ₀*(-H₀+T*a₀)) by ring] at hh
      simp only [sub_zero] at hh'
      linarith
    _ ≤ R := by linarith

theorem trial_kappa_interval :
    |2 * (12387581/10000000 : ℝ)^2 / Real.pi - 122113351373/125000000000| ≤
      1/1000000000000 := by
  rw [abs_sub_le_iff]
  constructor
  · suffices hh : 2 * (12387581/10000000 : ℝ)^2 / Real.pi ≤
        122113351373/125000000000 + 1/1000000000000 by linarith
    apply (div_le_iff₀ Real.pi_pos).2
    have h := Real.pi_gt_d20
    norm_num at *
    nlinarith
  · suffices hh : 122113351373/125000000000 - 1/1000000000000 ≤
        2 * (12387581/10000000 : ℝ)^2 / Real.pi by linarith
    apply (le_div_iff₀ Real.pi_pos).2
    have h := Real.pi_lt_d20
    norm_num at *
    nlinarith

/-- Evaluate the group at the outer cutoff, retaining its correlated initial
normalization coefficient in the two reciprocal corrections. -/
theorem compensatedPowerArcGroup_seed (β r κ w : ℝ) :
    compensatedPowerArcGroup β r κ w 1024 =
      w * (g β (2057-r) / g β 0) + κ *
        (-powerArcStieltjes β r (2057/2) / g β 0 +
          ((r+β)/(2*β)*(1/(2057/2)+((r-β)/2)/((1-β)*(2057/2)^2))) *
            (g β r / g β 0)) := by
  simp only [compensatedPowerArcGroup, compensatedStieltjes,
    stieltjesCorrectionC, stieltjesCorrectionD]
  norm_num only [Nat.cast_ofNat, even_two, Even.neg_pow, one_mul]
  simp only [div_mul_eq_div_div]
  congr 1; ring

end KsIndex.PowerArc
