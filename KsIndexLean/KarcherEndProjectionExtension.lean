module

public import KsIndexLean.KarcherQuotientEndDisk

@[expose] public section


/-! Extension of the parameter projection over the center of a quotient end chart. -/
noncomputable section
namespace KsIndex.KarcherData

variable {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m) {w : ℂ}
  (hw : w ∈ Surface.punctures k) (b : PuncturedPlane k)

/-- The root-coordinate region before removing its center. -/
def filledEndRootRegion : Set ℂ :=
  {t | t ^ m * endCoordinate k w b.val ∈ (endCoordinateChart hk hw).target}

/-- The base parameter extended to the center by the inverse end chart. -/
def filledEndParameter (t : ℂ) : ℂ :=
  (endCoordinateChart hk hw).symm (t ^ m * endCoordinate k w b.val)

lemma isOpen_filledEndRootRegion : IsOpen (filledEndRootRegion hk hw b (m := m)) :=
  (endCoordinateChart hk hw).open_target.preimage ((continuous_id.pow m).mul_const _)

include hm in
lemma zero_mem_filledEndRootRegion : (0 : ℂ) ∈ filledEndRootRegion hk hw b (m := m) := by
  change (0 : ℂ) ^ m * endCoordinate k w b.val ∈ (endCoordinateChart hk hw).target
  simpa only [zero_pow (Nat.ne_of_gt hm), zero_mul] using
    endCoordinateChart_zero_mem_target hk hw

include hm in
@[simp] theorem filledEndParameter_zero : filledEndParameter hk hw b (m := m) 0 = w := by
  unfold filledEndParameter
  rw [zero_pow (Nat.ne_of_gt hm), zero_mul]
  have he := (endCoordinateChart hk hw).left_inv (endCoordinateChart_mem_source hk hw)
  simpa only [endCoordinateChart_apply, endCoordinate_self hw] using he

lemma continuousOn_filledEndParameter :
    ContinuousOn (filledEndParameter hk hw b (m := m)) (filledEndRootRegion hk hw b (m := m)) := by
  exact (endCoordinateChart hk hw).symm.continuousOn.comp
    ((continuous_id.pow m).mul_const _).continuousOn (fun _ ht => ht)

include hm in
/-- Continuity at the added center, including approach through the punctured end. -/
theorem continuousAt_filledEndParameter_zero :
    ContinuousAt (filledEndParameter hk hw b (m := m)) 0 :=
  (continuousOn_filledEndParameter hk hw b).continuousAt
    ((isOpen_filledEndRootRegion hk hw b).mem_nhds
      (zero_mem_filledEndRootRegion hk hm hw b))

/-- In the base end coordinate, the extended projection is exactly a scaled m-th power. -/
theorem endCoordinate_filledEndParameter {t : ℂ}
    (ht : t ∈ filledEndRootRegion hk hw b (m := m)) :
    endCoordinate k w (filledEndParameter hk hw b (m := m) t) = t ^ m * endCoordinate k w b.val :=
  (endCoordinateChart hk hw).right_inv ht

lemma filledEndParameter_mem_source {t : ℂ}
    (ht : t ∈ filledEndRootRegion hk hw b (m := m)) :
    filledEndParameter hk hw b (m := m) t ∈ (endCoordinateChart hk hw).source :=
  (endCoordinateChart hk hw).map_target ht

/-- Only the center maps to a puncture within this extended end chart. -/
theorem filledEndParameter_not_mem_punctures {t : ℂ}
    (ht : t ∈ filledEndRootRegion hk hw b (m := m)) (hn : t ≠ 0) :
    filledEndParameter hk hw b (m := m) t ∉ Surface.punctures k := by
  intro hp
  have he := endCoordinate_filledEndParameter hk hw b ht
  rw [endCoordinate_at_puncture w hp] at he
  exact (mul_ne_zero (pow_ne_zero _ hn) (endCoordinate_ne_zero_at_finite w b)) he.symm

/-- The extension agrees with the original finite parameter of every point
of the actual quotient end source. -/
theorem filledEndParameter_quotientEndRoot (C : PeriodTarget)
    (x : HeightLift.PeriodQuotient (extendedEWMap hk b C) m)
    (z : PuncturedPlane k) (hz : z.val ∈ (endCoordinateChart hk hw).source)
    (hx : HeightLift.quotientProjection m x = finiteParameter z) :
    filledEndParameter hk hw b (m := m) (quotientEndRoot hk hm b w C x) = z.val := by
  unfold filledEndParameter
  rw [quotientEndRoot_pow_finite hk hm b z w C x hx,
    div_mul_cancel₀ _ (endCoordinate_ne_zero_at_finite w b)]
  exact (endCoordinateChart hk hw).left_inv hz

end KsIndex.KarcherData
