module

/-
# Conformal covariance of the potential under inversion-reflection

For `k ≥ 2` and `w ≠ 0`, the reflection `σ(w) = 1/w̄` satisfies

    potV k (σ w) = potV k w * ‖w‖⁴.

The potential is radial and `‖σ w‖ = ‖w‖⁻¹`, so the proof reduces to an
algebraic identity in the positive radius. The factor `‖w‖⁴` is the inverse
square of the conformal scale of σ. This transformation law is used to compare
the chart equations on the two sides of a seam in the Caccioppoli estimates.
-/
public import KsIndexLean.Surface

@[expose] public section


open Complex

noncomputable section

namespace KsIndex.PotVSigma

open KsIndex.Surface

/-- **Conformal covariance of the flat potential**: `potV k (1/w̄) = potV k w · ‖w‖⁴` for
`w ≠ 0`, `k ≥ 2`.  `σ = 1/w̄` sends `‖w‖ ↦ ‖w‖⁻¹`; `V_k` picks up the weight `‖w‖⁴ = |dσ|⁻²`. -/
lemma potV_sigma (k : ℕ) (hk : 2 ≤ k) {w : ℂ} (hw : w ≠ 0) :
    potV k (1 / (starRingEnd ℂ) w) = potV k w * ‖w‖ ^ 4 := by
  have hr : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  have hr2 : (0 : ℝ) < ‖w‖ ^ 2 := by positivity
  have hnorm : ‖(1 : ℂ) / (starRingEnd ℂ) w‖ = ‖w‖⁻¹ := by
    rw [norm_div, norm_one, Complex.norm_conj, one_div]
  have h2 : 2 * k - 2 = (2 * k - 4) + 2 := by omega
  unfold potV
  rw [hnorm, h2, pow_add, pow_add]
  simp only [inv_pow]
  set A : ℝ := ‖w‖ ^ (2 * k - 4) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  have hAmul : (0 : ℝ) < A * ‖w‖ ^ 2 := mul_pos hApos hr2
  have hAne : A ≠ 0 := hApos.ne'
  have hr2ne : ‖w‖ ^ 2 ≠ 0 := hr2.ne'
  have hd1 : A * ‖w‖ ^ 2 + 1 ≠ 0 := (show (0 : ℝ) < A * ‖w‖ ^ 2 + 1 by linarith).ne'
  have hd2 : (A * ‖w‖ ^ 2)⁻¹ + 1 ≠ 0 :=
    (show (0 : ℝ) < (A * ‖w‖ ^ 2)⁻¹ + 1 by have := inv_pos.mpr hAmul; linarith).ne'
  field_simp
  ring

end KsIndex.PotVSigma
