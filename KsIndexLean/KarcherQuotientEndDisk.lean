module

public import KsIndexLean.KarcherQuotientEndChart

@[expose] public section


/-! Each quotient end-chart range contains a punctured disk centered at zero. -/
noncomputable section
namespace KsIndex.KarcherData

variable {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m) {w : ℂ}
  (hw : w ∈ Surface.punctures k) (b : PuncturedPlane k) (C : PeriodTarget)

include hm in
/-- The root target is the punctured preimage of the base end-coordinate target. -/
lemma quotientEndTarget_eq : quotientEndTarget hk hw b (m := m) =
    {t : ℂ | t ^ m * endCoordinate k w b.val ∈ (endCoordinateChart hk hw).target ∧
      t ≠ 0} := by
  ext t
  constructor
  · rintro ⟨z, hz, he⟩
    have hc := endCoordinate_ne_zero_at_finite w b
    have hmz : m ≠ 0 := Nat.ne_of_gt hm
    refine ⟨?_, ?_⟩
    · rw [he, div_mul_cancel₀ _ hc]
      exact (endCoordinateChart hk hw).map_source hz
    · intro ht
      have hn := div_ne_zero (endCoordinate_ne_zero_at_finite w z) hc
      apply hn
      rw [← he, ht, zero_pow hmz]
  · rintro ⟨ht, hn⟩
    have hc := endCoordinate_ne_zero_at_finite w b
    have hzero : t ^ m * endCoordinate k w b.val ≠ 0 := mul_ne_zero (pow_ne_zero _ hn) hc
    have hi : t ^ m * endCoordinate k w b.val ∈
        endCoordinateChart hk hw ''
          {z | z ∈ (endCoordinateChart hk hw).source ∧ z ∉ Surface.punctures k} := by
      rw [endCoordinateChart_punctured_image]
      exact ⟨ht, hzero⟩
    obtain ⟨z, ⟨hz, hp⟩, he⟩ := hi
    refine ⟨⟨z, hp⟩, hz, ?_⟩
    change t ^ m = endCoordinate k w z / endCoordinate k w b.val
    apply (eq_div_iff hc).mpr
    exact he.symm

include hm in
/-- The local coordinate contains every sufficiently small nonzero root. -/
theorem exists_punctured_ball_subset_quotientEndTarget :
    ∃ ε : ℝ, 0 < ε ∧ {t : ℂ | t ∈ Metric.ball 0 ε ∧ t ≠ 0} ⊆
      quotientEndTarget hk hw b (m := m) := by
  let U : Set ℂ := {t | t ^ m * endCoordinate k w b.val ∈
    (endCoordinateChart hk hw).target}
  have ho : IsOpen U := (endCoordinateChart hk hw).open_target.preimage
    ((continuous_id.pow m).mul_const _)
  have hz : (0 : ℂ) ∈ U := by
    change (0 : ℂ) ^ m * endCoordinate k w b.val ∈ (endCoordinateChart hk hw).target
    simpa only [zero_pow (Nat.ne_of_gt hm), zero_mul] using
      endCoordinateChart_zero_mem_target hk hw
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp ho 0 hz
  refine ⟨ε, hε, ?_⟩
  intro t ht
  rw [quotientEndTarget_eq hk hm hw b]
  exact ⟨hsub ht.1, ht.2⟩

/-- Restriction of the actual root chart to any contained punctured disk. -/
def quotientEndDiskHomeomorph (hF : Continuous (extendedEWMap hk b C))
    (ε : ℝ) (hε : {t : ℂ | t ∈ Metric.ball 0 ε ∧ t ≠ 0} ⊆
      quotientEndTarget hk hw b (m := m)) :
    {x : quotientEndSource hk hw b C (m := m) //
      quotientEndRoot hk hm b w C x.val ∈ Metric.ball 0 ε ∧
        quotientEndRoot hk hm b w C x.val ≠ 0} ≃ₜ
      {t : ℂ // t ∈ Metric.ball 0 ε ∧ t ≠ 0} :=
  (quotientEndRoot_source_isOpenEmbedding hk hm hw b C hF).isEmbedding.homeomorphOfSubsetRange
    (s := {t : ℂ | t ∈ Metric.ball 0 ε ∧ t ≠ 0})
    (by rw [quotientEndRoot_source_range]; exact hε)

@[simp] theorem quotientEndDiskHomeomorph_apply
    (hF : Continuous (extendedEWMap hk b C)) (ε : ℝ)
    (hε : {t : ℂ | t ∈ Metric.ball 0 ε ∧ t ≠ 0} ⊆
      quotientEndTarget hk hw b (m := m))
    (x : {x : quotientEndSource hk hw b C (m := m) //
      quotientEndRoot hk hm b w C x.val ∈ Metric.ball 0 ε ∧
        quotientEndRoot hk hm b w C x.val ≠ 0}) :
    (quotientEndDiskHomeomorph hk hm hw b C hF ε hε x).val =
      quotientEndRoot hk hm b w C x.val.val := rfl

end KsIndex.KarcherData
