module

public import KsIndexLean.KarcherHeightRoot
public import KsIndexLean.KarcherEndCoordinate

@[expose] public section


/-! Root coordinates for both types of EW end, with the normalization at the
chosen integration basepoint retained explicitly. -/
noncomputable section
namespace KsIndex.KarcherData

/-- Choose the height root or its reciprocal to match the simple-zero
coordinate of the selected end. -/
def endRoot (k m : ℕ) (b w z : ℂ) (h : ℝ) : ℂ :=
  if w ^ k = Complex.I then heightRoot m (heightCayley k z / heightCayley k b) h
  else (heightRoot m (heightCayley k z / heightCayley k b) h)⁻¹

lemma endRoot_ne_zero (k m : ℕ) (b w z : ℂ) (h : ℝ) : endRoot k m b w z h ≠ 0 := by
  unfold endRoot
  split_ifs
  · exact heightRoot_ne_zero _ _ _
  · exact inv_ne_zero (heightRoot_ne_zero _ _ _)

/-- Both end types yield the corresponding normalized simple-zero coordinate
when the root is raised to the m-th power. -/
theorem lift_endRoot_pow {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m)
    (b z : PuncturedPlane k) (w : ℂ) (C : PeriodTarget)
    (q : PeriodicEWCarrier hk b C)
    (hq : HeightLift.projection q = finiteParameter z) :
    endRoot k m b.val w z.val (HeightLift.height q) ^ m =
      endCoordinate k w z.val / endCoordinate k w b.val := by
  rw [endCoordinate_eq_heightCayley, endCoordinate_eq_heightCayley]
  unfold endRoot
  split_ifs
  · exact lift_heightRoot_pow hk hm b z C q hq
  · rw [inv_pow, lift_heightRoot_pow hk hm b z C q hq]
    simp only [inv_div]
    field_simp

/-- The signed end root is invariant under the same m-fold height periods. -/
theorem endRoot_period {m : ℕ} (hm : 0 < m) (k : ℕ) (b w z : ℂ)
    (h : ℝ) (n : ℤ) :
    endRoot k m b w z (h + ((n * (m : ℤ) : ℤ) : ℝ) * (2 * Real.pi)) =
      endRoot k m b w z h := by
  unfold endRoot
  rw [heightRoot_period hm]

end KsIndex.KarcherData
