module

public import KsIndexLean.BallPolar
public import KsIndexLean.CutoffContinuity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section


/-! Exact radial integrals for the EW curvature potential. -/
noncomputable section
open Set MeasureTheory intervalIntegral
namespace KsIndex.KarcherData

lemma radial_quotient_hasDerivAt {n : ℕ} (_hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt (fun x : ℝ => x ^ n / (1 + x ^ n))
      ((n : ℝ) * r ^ (n - 1) / (1 + r ^ n) ^ 2) r := by
  have hd := ((hasDerivAt_id r).pow n).div
    ((hasDerivAt_const r (1 : ℝ)).add ((hasDerivAt_id r).pow n))
    (show (1 : ℝ) + r ^ n ≠ 0 by positivity)
  simp only [id_eq, Pi.pow_apply, Pi.add_apply, mul_one, zero_add] at hd
  convert hd using 1
  all_goals first | rfl | ring

lemma integral_radial_quotient {n : ℕ} (hn : 0 < n) :
    (∫ r in (0 : ℝ)..1, (n : ℝ) * r ^ (n - 1) / (1 + r ^ n) ^ 2) = 1 / 2 := by
  have hc : ContinuousOn (fun r : ℝ => (n : ℝ) * r ^ (n - 1) / (1 + r ^ n) ^ 2)
      (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.div (continuous_const.mul (continuous_id.pow _)).continuousOn
      ((continuous_const.add (continuous_id.pow _)).pow 2).continuousOn
    intro r hr
    have : 0 ≤ r := hr.1
    dsimp
    positivity
  have hi : IntervalIntegrable (fun r : ℝ =>
      (n : ℝ) * r ^ (n - 1) / (1 + r ^ n) ^ 2) volume 0 1 :=
    hc.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hd : ∀ r ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun x : ℝ => x ^ n / (1 + x ^ n))
        ((n : ℝ) * r ^ (n - 1) / (1 + r ^ n) ^ 2) r := by
    intro r hr
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
    exact radial_quotient_hasDerivAt hn hr.1
  rw [integral_eq_sub_of_hasDerivAt hd hi]
  norm_num [Nat.ne_of_gt hn]

/-- The flat EW potential has an exact integral on one disk. -/
theorem integral_disk_potV {k : ℕ} (hk : 2 ≤ k) :
    (∫ w in Metric.ball (0 : ℂ) 1, Surface.potV k w) =
      4 * Real.pi * ((k : ℝ) - 1) := by
  rw [BallPolar.setIntegral_ball_polar (CutoffContinuity.continuous_potV k)]
  have hcast : ((2 * k - 2 : ℕ) : ℝ) = 2 * ((k : ℝ) - 1) := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul]
    norm_num
    ring
  have he : (∫ r in (0 : ℝ)..1, ∫ θ in (0 : ℝ)..(2 * Real.pi),
      r * Surface.potV k ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) =
      ∫ r in (0 : ℝ)..1, (8 * Real.pi * ((k : ℝ) - 1)) *
        (((2 * k - 2 : ℕ) : ℝ) * r ^ ((2 * k - 2) - 1) /
          (1 + r ^ (2 * k - 2)) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr0 : 0 ≤ r := (uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1) ▸ hr).1
    have hnorm (θ : ℝ) : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
      simp [Complex.norm_exp, abs_of_nonneg hr0]
    simp only [Surface.potV, hnorm, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    have hp : r ^ ((2 * k - 2) - 1) = r * r ^ (2 * k - 4) := by
      rw [show (2 * k - 2) - 1 = (2 * k - 4) + 1 by omega, pow_succ']
    rw [hcast, hp]
    ring
  rw [he, intervalIntegral.integral_const_mul, integral_radial_quotient (by omega)]
  ring

end KsIndex.KarcherData
