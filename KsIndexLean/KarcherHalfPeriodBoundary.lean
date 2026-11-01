module

public import KsIndexLean.KarcherHalfPeriodDomain

@[expose] public section


/-! Boundary heights with the exact alternating arc convention of ewcover. -/
noncomputable section
namespace KsIndex.KarcherData
open Set

lemma halfPeriod_boundary_levels {k : ℕ} (hk : 2 ≤ k)
    (b w : PuncturedPlane k) (hb : b.val = 1) (C : PeriodTarget)
    (q : PaperHalfPeriod hk b C) (hq : HeightLift.projection q.val = finiteParameter w)
    (hw : ‖w.val‖ = 1) :
    HeightLift.height q.val + Real.pi = 0 ∨ HeightLift.height q.val + Real.pi = Real.pi := by
  have hs := (sin_lift_height_shift_zero_iff hk b w hb C q.val hq).mpr hw
  by_cases he : HeightLift.height q.val + Real.pi = Real.pi
  · exact Or.inr he
  · left
    apply (Real.sin_eq_zero_iff_of_lt_of_lt _ _).mp hs
    · linarith [q.property.1, Real.pi_pos]
    · exact lt_of_le_of_ne q.property.2 he

/-- Height zero is exactly the paper's arc family Θ[k,0]. -/
theorem halfPeriod_height_zero_iff_arc {k : ℕ} (hk : 2 ≤ k)
    (b w : PuncturedPlane k) (hb : b.val = 1) (C : PeriodTarget)
    (q : PaperHalfPeriod hk b C) (hq : HeightLift.projection q.val = finiteParameter w) :
    HeightLift.height q.val + Real.pi = 0 ↔ w.val ∈ Surface.arc k 0 := by
  change _ ↔ ‖w.val‖ = 1 ∧ (-1 : ℝ) ^ 0 * (w.val ^ k).re < 0
  simp only [pow_zero, one_mul]
  constructor
  · intro hz
    refine ⟨(sin_lift_height_shift_zero_iff hk b w hb C q.val hq).mp ?_,
      (cos_lift_height_shift_pos_iff hk b w hb C q.val hq).mp ?_⟩
    · rw [hz, Real.sin_zero]
    · rw [hz, Real.cos_zero]; norm_num
  · rintro ⟨hw, ha⟩
    rcases halfPeriod_boundary_levels hk b w hb C q hq hw with hz | hp
    · exact hz
    · have hh := (cos_lift_height_shift_pos_iff hk b w hb C q.val hq).mpr ha
      rw [hp, Real.cos_pi] at hh
      norm_num at hh

/-- Height π is exactly the paper's other arc family Θ[k,1]. -/
theorem halfPeriod_height_pi_iff_arc {k : ℕ} (hk : 2 ≤ k)
    (b w : PuncturedPlane k) (hb : b.val = 1) (C : PeriodTarget)
    (q : PaperHalfPeriod hk b C) (hq : HeightLift.projection q.val = finiteParameter w) :
    HeightLift.height q.val + Real.pi = Real.pi ↔ w.val ∈ Surface.arc k 1 := by
  change _ ↔ ‖w.val‖ = 1 ∧ (-1 : ℝ) ^ 1 * (w.val ^ k).re < 0
  simp only [pow_one, neg_one_mul, neg_lt_zero]
  constructor
  · intro hz
    refine ⟨(sin_lift_height_shift_zero_iff hk b w hb C q.val hq).mp ?_,
      (cos_lift_height_shift_neg_iff hk b w hb C q.val hq).mp ?_⟩
    · rw [hz, Real.sin_pi]
    · rw [hz, Real.cos_pi]; norm_num
  · rintro ⟨hw, ha⟩
    rcases halfPeriod_boundary_levels hk b w hb C q hq hw with hz | hp
    · have hh := (cos_lift_height_shift_neg_iff hk b w hb C q.val hq).mpr ha
      rw [hz, Real.cos_zero] at hh
      norm_num at hh
    · exact hp

end KsIndex.KarcherData
