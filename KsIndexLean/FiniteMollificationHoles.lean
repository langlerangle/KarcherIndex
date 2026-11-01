module

public import KsIndexLean.MollificationHoles
public import KsIndexLean.PunctureCutoffP
public import KsIndexLean.JacobiFamily

@[expose] public section


open Set Filter Topology MeasureTheory Metric
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket KsIndex.SingleDisk KsIndex.Surface

/-- Finitely many punctures admit one fixed smaller radius and one eventual scale. -/
theorem reflected_mollifier_finite_holes (s : ℂ) (P : Finset ℂ) {u : ℂ → ℂ}
    (hp : ∀ p ∈ P, ‖p‖ = 1)
    (hu : ∀ p ∈ P, ∃ R : ℝ, 0 < R ∧
      ∀ᵐ w ∂volume, dist w p < R → u w = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, ∀ p ∈ P, ∀ z, dist z p < δ →
      reflectionAverage s (compactMollify (shrinkingMollifier n) u) z = 0 := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, Eventually.of_forall (by simp)⟩
  | @insert p P hnot ih =>
    obtain ⟨R, hR, hzero⟩ := hu p (Finset.mem_insert_self p P)
    obtain ⟨a, ha, hea⟩ := reflected_mollifier_zero_ball s
      (hp p (Finset.mem_insert_self p P)) hR hzero
    obtain ⟨b, hb, heb⟩ := ih
      (fun q hq => hp q (Finset.mem_insert_of_mem hq))
      (fun q hq => hu q (Finset.mem_insert_of_mem hq))
    refine ⟨min a b, lt_min ha hb, ?_⟩
    filter_upwards [hea, heb] with n hn hm
    intro q hq z hz
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hn z (lt_of_lt_of_le hz (min_le_left _ _))
    · exact hm q hq z (lt_of_lt_of_le hz (min_le_right _ _))

/-- The actual paper puncture-support predicate holds for the reflected smooth sequence. -/
theorem reflected_mollifier_suppAwayP1 (k : ℕ) (hk : 1 ≤ k) (s : ℂ) {u : ℂ → ℂ}
    (hu : ∀ p ∈ punctures k, ∃ R : ℝ, 0 < R ∧
      ∀ᵐ w ∂volume, dist w p < R → u w = 0) :
    ∀ᶠ n in atTop,
      SuppAwayP1 k (closedDiskRestriction
        (reflectionAverage s (compactMollify (shrinkingMollifier n) u))) := by
  obtain ⟨δ, hδ, he⟩ := reflected_mollifier_finite_holes s (KsIndex.PunctureCutoff.pF k)
    (fun p hp => KsIndex.JacobiFamily.punctures_norm_eq_one hk
      ((KsIndex.PunctureCutoff.mem_pF hk).mp hp))
    (fun p hp => hu p ((KsIndex.PunctureCutoff.mem_pF hk).mp hp))
  filter_upwards [he] with n hn
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  obtain ⟨p, hp, hwp⟩ := hw
  have hz := hn p ((KsIndex.PunctureCutoff.mem_pF hk).mpr hp) w
    (by simpa only [dist_eq_norm] using hwp)
  simp [closedDiskRestriction, hz]

end KsIndex.Trace
