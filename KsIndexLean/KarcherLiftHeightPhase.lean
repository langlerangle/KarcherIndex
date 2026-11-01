module

public import KsIndexLean.KarcherHeightCayley

@[expose] public section


/-! The complex phase of the rational height coordinate on the actual EW lift.
The basepoint factor is retained explicitly to fix the normalization used by
root coordinates near the ends. -/

noncomputable section
namespace KsIndex.KarcherData
open Complex

/-- Every sheet of the intrinsic height lift has the phase obtained from the
actual EW contour integral. -/
theorem exp_lift_height {k : ℕ} (hk : 2 ≤ k)
    (b w : PuncturedPlane k) (C : PeriodTarget)
    (q : PeriodicEWCarrier hk b C)
    (hq : HeightLift.projection q = finiteParameter w) :
    Complex.exp (I * (HeightLift.height q : ℂ)) =
      (heightCayley k w.val / heightCayley k b.val) /
        (‖heightCayley k w.val / heightCayley k b.val‖ : ℂ) := by
  have hv : projectPeriod (HeightLift.ambient q) = descendedIntegral hk b w := by
    rw [HeightLift.project_ambient, hq, extendedEWMap_finite]
  obtain ⟨D, hs, ht, hD, he⟩ := exists_chain_with_real_integral hk b w
    (HeightLift.ambient q) hv
  have hz : (D.contour (coeff3 k)).re = HeightLift.height q :=
    congrArg (fun v : AmbientTriple => v.2.2) he
  have hh := exp_chain_real_vertical D hD
  rw [hz, hs, ht] at hh
  exact hh

/-- At basepoint 1 the phase is that of the Cayley coordinate divided by i. -/
theorem exp_lift_height_base_one {k : ℕ} (hk : 2 ≤ k)
    (b w : PuncturedPlane k) (hb : b.val = 1) (C : PeriodTarget)
    (q : PeriodicEWCarrier hk b C)
    (hq : HeightLift.projection q = finiteParameter w) :
    Complex.exp (I * (HeightLift.height q : ℂ)) =
      (heightCayley k w.val / I) / (‖heightCayley k w.val‖ : ℂ) := by
  rw [exp_lift_height hk b w C q hq, hb, heightCayley_one]
  simp

end KsIndex.KarcherData
