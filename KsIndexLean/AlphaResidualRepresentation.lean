module

public import KsIndexLean.AlphaResidualCertificate

@[expose] public section


/-! A justified transpose formula for the circle form. Absolute summability
of the double series is an explicit hypothesis, to be supplied for the trial. -/
noncomputable section
namespace KsIndex.AlphaResidual
open CircleQ Statements

def transposeCoefficient (w : ℤ → ℂ) (n : ℤ) : ℂ :=
  ∑' m : ℤ, (sigM m : ℂ) * (starRingEnd ℂ) (convS w m) * (chat (m-n) : ℂ)

def coefficientResidual (s : ℝ) (w : ℤ → ℂ) (n : ℤ) : ℂ :=
  (sigP n : ℂ) * (starRingEnd ℂ) (w n) + (s : ℂ)^2 * transposeCoefficient w n

/-- Fubini identifies the form on an arbitrary domain test vector, provided
its double series is absolutely summable. -/
theorem Bform_eq_coefficientResidual {s : ℝ} {w z : ℤ → ℂ}
    (hw : MemDom w) (hz : MemDom z)
    (hdouble : Summable (fun p : ℤ × ℤ =>
      (sigM p.1 : ℂ) * (starRingEnd ℂ) (convS w p.1) *
        (chat (p.1-p.2) : ℂ) * z p.2)) :
    Bform s w z = ∑' n, coefficientResidual s w n * z n := by
  have hp := summable_pairP hw.1 hz.1
  have ht : Summable (fun n => transposeCoefficient w n * z n) := by
    apply hdouble.prod_symm.prod.congr
    intro n
    change (∑' m : ℤ, (sigM m : ℂ) * (starRingEnd ℂ) (convS w m) * (chat (m-n) : ℂ) * z n) = _
    rw [tsum_mul_right]
    rfl
  have he : (∑' m : ℤ, (sigM m : ℂ) *
      ((starRingEnd ℂ) (convS w m) * convS z m)) =
      ∑' n, transposeCoefficient w n * z n := by
    calc
      _ = ∑' m : ℤ, ∑' n : ℤ, (sigM m : ℂ) *
          (starRingEnd ℂ) (convS w m) * (chat (m-n) : ℂ) * z n := by
        apply tsum_congr
        intro m
        rw [show convS z m = ∑' n : ℤ, (chat (m-n) : ℂ) * z n from rfl]
        rw [← mul_assoc, ← tsum_mul_left]
        apply tsum_congr
        intro n
        ring
      _ = ∑' n : ℤ, ∑' m : ℤ, (sigM m : ℂ) *
          (starRingEnd ℂ) (convS w m) * (chat (m-n) : ℂ) * z n :=
        hdouble.tsum_comm.symm
      _ = _ := by simp only [transposeCoefficient, tsum_mul_right]
  rw [Bform, he]
  rw [← tsum_mul_left, ← hp.tsum_add (ht.mul_left ((s : ℂ)^2))]
  apply tsum_congr
  intro n
  simp only [coefficientResidual]
  ring

/-- The head residual can be set to zero for the certificate's test space. -/
theorem Bform_eq_headZeroResidual {s : ℝ} {w z : ℤ → ℂ}
    (hw : MemDom w) (hz : MemDom z) (hz0 : z 0 = 0)
    (hdouble : Summable (fun p : ℤ × ℤ =>
      (sigM p.1 : ℂ) * (starRingEnd ℂ) (convS w p.1) *
        (chat (p.1-p.2) : ℂ) * z p.2)) :
    Bform s w z = ∑' n, (if n = 0 then 0 else coefficientResidual s w n) * z n := by
  rw [Bform_eq_coefficientResidual hw hz hdouble]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn, hz0]
  · simp [hn]

end KsIndex.AlphaResidual
