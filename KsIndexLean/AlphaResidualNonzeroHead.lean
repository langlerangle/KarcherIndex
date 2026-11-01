module

public import KsIndexLean.AlphaResidualCertificate

@[expose] public section


/-! Scale-invariant residual certificates for trials with nonzero head coefficient. -/
noncomputable section
namespace KsIndex.AlphaResidual
open CircleQ Statements

/-- The residual-energy comparison may be checked before head normalization. -/
theorem gam_pos_of_coefficient_residual_nonzero_head {s : ℝ} {w R : ℤ → ℂ}
    (hs : 0 < s) (hw : MemDom w) (hw0 : w 0 ≠ 0)
    (hR : Summable (fun n => ‖R n‖ ^ 2 / residualWeight n))
    (hrep : ∀ z : ℤ → ℂ, MemDom z → z 0 = 0 →
      Bform s w z = ∑' n, R n * z n)
    (hmargin : (∑' n, ‖R n‖ ^ 2 / residualWeight n) < Qform s w) :
    0 < gam s := by
  let c : ℂ := (w 0)⁻¹
  let R' : ℤ → ℂ := fun n => (starRingEnd ℂ) c * R n
  have hc : 0 < ‖c‖^2 := pow_pos (norm_pos_iff.mpr (inv_ne_zero hw0)) 2
  have he (n : ℤ) : ‖R' n‖^2 / residualWeight n =
      ‖c‖^2 * (‖R n‖^2 / residualWeight n) := by
    simp only [R', norm_mul, Complex.norm_conj, mul_pow]
    ring
  have hR' : Summable (fun n => ‖R' n‖^2 / residualWeight n) := by
    simp_rw [he]
    exact hR.mul_left _
  apply gam_pos_of_coefficient_residual hs (memDom_smul c hw)
    (by simp [c, hw0]) hR'
  · intro z hz hz0
    rw [Bform_smul_left, hrep z hz hz0, ← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [R']
    ring
  · simp_rw [he]
    rw [tsum_mul_left, Qform_smul]
    exact mul_lt_mul_of_pos_left hmargin hc

end KsIndex.AlphaResidual
