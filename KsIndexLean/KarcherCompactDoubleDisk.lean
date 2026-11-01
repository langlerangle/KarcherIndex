module

public import KsIndexLean.KarcherCompactVertexLabels

@[expose] public section


/-! In a single period the compactification is two closed disks glued along the circle. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.DiskCompactification
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma filledRel_one_period (p q : Copies 1) :
    filledRel (k := k) p q ↔ p.2 = q.2 ∧ (p.1 = q.1 ∨ ‖p.2.val‖ = 1) := by
  constructor
  · rintro ⟨hz,hp | hi | hn | hn⟩
    · exact ⟨hz, Or.inr (puncture_norm h.out hp)⟩
    · exact ⟨hz, Or.inl hi⟩
    · exact ⟨hz, Or.inr hn.2.1⟩
    · exact ⟨hz, Or.inr hn.2.1⟩
  · rintro ⟨hz,hi | hn⟩
    · exact ⟨hz, Or.inr (Or.inl hi)⟩
    · rw [filledRel_closed_formula]
      refine ⟨hz, ?_⟩
      rcases p with ⟨i,z⟩
      rcases q with ⟨j,v⟩
      dsimp only at *
      have hi : i = 0 ∨ i = 1 := by fin_cases i <;> first | exact Or.inl rfl | exact Or.inr rfl
      have hj : j = 0 ∨ j = 1 := by fin_cases j <;> first | exact Or.inl rfl | exact Or.inr rfl
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · right; right
        by_cases hp : 0 ≤ (z.val ^ k).re
        · left
          refine ⟨by decide, hn, ?_⟩
          simp only [zero_add, map_one, show (1 : ZMod 2).val = 1 from rfl, pow_one, neg_one_mul]
          linarith
        · right
          refine ⟨by decide, hn, ?_⟩
          change 1 * (z.val ^ k).re ≤ 0
          linarith
      · right; right
        by_cases hp : (z.val ^ k).re ≤ 0
        · left
          refine ⟨by decide, hn, ?_⟩
          change 1 * (z.val ^ k).re ≤ 0
          linarith
        · right
          refine ⟨by decide, hn, ?_⟩
          simp only [zero_add, map_one, show (1 : ZMod 2).val = 1 from rfl, pow_one, neg_one_mul]
          linarith
      · exact Or.inr (Or.inl rfl)

/-- The filled equivalence relation for one period is independent of the number of ends. -/
lemma filledRel_one_period_independent {l : ℕ} [Fact (2 ≤ l)] (p q : Copies 1) :
    filledRel (k := k) p q ↔ filledRel (k := l) p q := by
  rw [filledRel_one_period, filledRel_one_period]

/-- Changing the number of marked ends does not change the compact one-period space. -/
def onePeriodChangeEnds (l : ℕ) [Fact (2 ≤ l)] : FilledChain k 1 ≃ₜ FilledChain l 1 where
  toEquiv := Quotient.congrRight (filledRel_one_period_independent (k := k) (l := l))
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact continuous_quotient_mk'
  continuous_invFun := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact continuous_quotient_mk'

lemma onePeriodChangeEnds_apply (l : ℕ) [Fact (2 ≤ l)] (p : Copies 1) :
    onePeriodChangeEnds (k := k) l (Quotient.mk (filledSetoid k 1) p) =
      Quotient.mk (filledSetoid l 1) p := rfl

end KsIndex.KarcherData.DiskCompactification
