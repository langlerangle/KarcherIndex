module

public import KsIndexLean.AlphaRemarkTrial
public import KsIndexLean.AlphaOppositeHalfIdentity

@[expose] public section


/-! # The kernel applied twice returns the trial: `U = w`

The
`U`-moment of the opposite-half identity is `U(n) = ∑' m, chat (m-n) · (convS trial) m`.
The kernel satisfies the half-integer reflection `chat (-d-1) = chat d`, so this
sum is `convS (convS trial) (n-1)`; the convolution theorem shifts each
normalized power field by one, hence twice returns the trial itself. -/

noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ PowerArc

lemma odd_den_ne_zero' (d : ℤ) : (2 * (d : ℝ) + 1) ≠ 0 := by
  have h : ((2 * d + 1 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
  intro hc
  apply h
  push_cast
  linarith

/-- The convolution kernel is symmetric under the half-integer reflection. -/
lemma chat_reflect (d : ℤ) : chat (-d - 1) = chat d := by
  have h1 : (-1 : ℝ) ^ (-d - 1) = (-1) ^ (-d) * (-1) ^ (1 : ℤ) :=
    KsIndex.OppositeHalf.negOne_zpow_sub (-d) 1
  have h2 : (-1 : ℝ) ^ (-d) = (-1) ^ (0 : ℤ) * (-1) ^ d := by
    simpa using KsIndex.OppositeHalf.negOne_zpow_sub 0 d
  have hden := odd_den_ne_zero' d
  simp only [chat, h1, h2]
  have hcast : ((-d - 1 : ℤ) : ℝ) = -(d : ℝ) - 1 := by push_cast; ring
  rw [hcast]
  have hden2 : (2 * (-(d : ℝ) - 1) + 1) ≠ 0 := by
    intro hc
    apply hden
    linarith
  field_simp
  ring

/-- `convS trial` is itself a power trial, with every shift advanced by one. -/
lemma convS_trial_eq_powerTrial :
    convS trial = powerTrial Finset.univ exponent (fun i => shift i + 1) coefficient := by
  funext m
  rw [convS_trial]
  simp only [powerTrial, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    normalizedPowerField_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (2 * (m : ℝ) + ((shift i + 1 : ℤ) : ℝ)) = 2 * (m : ℝ) + ((shift i : ℝ) + 1) by
    push_cast; ring]

/-- The kernel correlation of `convS trial` at index `n` is
`trial n` itself. (The evaluation of `convS (convS trial)` at `n - 1` is an
intermediate step of the proof, not part of the statement: the result is at
index `n`.) -/
theorem tsum_chat_convS_trial (n : ℤ) :
    ∑' m : ℤ, (chat (m - n) : ℂ) * convS trial m = trial n := by
  have hker : (fun m : ℤ => (chat (m - n) : ℂ) * convS trial m) =
      fun m : ℤ => (chat ((n - 1) - m) : ℂ) * convS trial m := by
    funext m
    rw [show (n - 1) - m = -(m - n) - 1 by ring, chat_reflect]
  rw [hker]
  have hU : ∑' m : ℤ, (chat ((n - 1) - m) : ℂ) * convS trial m =
      convS (convS trial) (n - 1) := rfl
  rw [hU, convS_trial_eq_powerTrial,
    convS_powerTrial Finset.univ exponent (fun i => shift i + 1) coefficient
      (fun i _ => exponent_pos i) (n - 1)]
  simp only [trial, powerTrial, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    normalizedPowerField_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (2 * ((n - 1 : ℤ) : ℝ) + ((shift i + 1 : ℤ) + 1 : ℝ)) =
      2 * (n : ℝ) + ((shift i : ℤ) : ℝ) by push_cast; ring]

end KsIndex.AlphaRemarkTrial
