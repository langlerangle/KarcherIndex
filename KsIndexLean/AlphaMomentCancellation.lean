module

public import KsIndexLean.AlphaRemainderIdentity
public import KsIndexLean.AlphaTrialMomentReduced

@[expose] public section


/-! Cancellation-first formulas for the two shared remainder moments.
Intervals are propagated after eliminating the repeated reduced moment. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open OppositeHalf

theorem Upos_eq_cancelled : Upos = 12 * trialMomentPrefix +
    2 * reducedMomentUpper (14/3) - 2 * reducedMomentLower (13/3) := by
  rw [Upos, signedTrialMoment_eq_reduced]
  ring

theorem Uneg_eq_cancelled : Uneg = 12 * trialMomentPrefix +
    2 * reducedMomentLower (13/3) - 2 * reducedMomentUpper (14/3) := by
  rw [Uneg, signedTrialMoment_eq_reduced]
  ring

theorem Upos_add_Uneg : Upos + Uneg = 24 * trialMomentPrefix := by
  rw [Upos_eq_cancelled, Uneg_eq_cancelled]
  ring

/-- A joint supplier preserves the cancellation before propagating endpoint errors. -/
theorem moments_enclosed (pl ph ll lh hl hh : ℝ)
    (hp : pl ≤ trialMomentPrefix ∧ trialMomentPrefix ≤ ph)
    (hlower : ll ≤ reducedMomentLower (13/3) ∧ reducedMomentLower (13/3) ≤ lh)
    (hupper : hl ≤ reducedMomentUpper (14/3) ∧ reducedMomentUpper (14/3) ≤ hh) :
    (12*pl + 2*hl - 2*lh ≤ Upos ∧ Upos ≤ 12*ph + 2*hh - 2*ll) ∧
    (12*pl + 2*ll - 2*hh ≤ Uneg ∧ Uneg ≤ 12*ph + 2*lh - 2*hl) := by
  rw [Upos_eq_cancelled, Uneg_eq_cancelled]
  rcases hp with ⟨hp0, hp1⟩
  rcases hlower with ⟨hl0, hl1⟩
  rcases hupper with ⟨hh0, hh1⟩
  constructor <;> constructor <;> linarith

end KsIndex.AlphaRemarkTrial

#print axioms KsIndex.AlphaRemarkTrial.moments_enclosed
