module

public import Mathlib

@[expose] public section


/-! Rational compensation of a Stieltjes residual recurrence.

Removing explicit reciprocal terms improves the decay of the forcing without
altering the homogeneous recurrence. These are algebraic identities only.
-/

namespace KsIndex.AlphaResidual

/-- Removing the leading reciprocal term exposes a third-order forcing term. -/
theorem first_compensated_step (A B z C f fnext : ℝ)
    (hz : z ≠ 0) (hz1 : z + 1 ≠ 0) (hd : z + 1 - A ≠ 0)
    (hstep : fnext = (z + 1 - B) / (z + 1 - A) * f -
      C * (B - A - 1) / (z * (z + 1 - A))) :
    fnext + C / (z + 1) =
      (z + 1 - B) / (z + 1 - A) * (f + C / z) +
        C * A / (z * (z + 1) * (z + 1 - A)) := by
  rw [hstep]
  field_simp
  ring

/-- Removing the next reciprocal term exposes a fourth-order forcing term.
The coefficient relation is encoded by `D * (A - B + 2)` in the hypothesis. -/
theorem second_compensated_step (A B z D f fnext : ℝ)
    (hz : z ≠ 0) (hz1 : z + 1 ≠ 0) (hd : z + 1 - A ≠ 0)
    (hstep : fnext = (z + 1 - B) / (z + 1 - A) * f +
      D * (A - B + 2) / (z * (z + 1) * (z + 1 - A))) :
    fnext + D / (z + 1) ^ 2 =
      (z + 1 - B) / (z + 1 - A) * (f + D / z ^ 2) +
        D * ((A + B - 1) * z + B - 1) /
          (z ^ 2 * (z + 1) ^ 2 * (z + 1 - A)) := by
  rw [hstep]
  field_simp
  ring

end KsIndex.AlphaResidual
