module

public import KsIndexLean.KarcherFilledDiskComplement
public import KsIndexLean.KarcherPolynomialRoots

@[expose] public section


/-! The compact Hausdorff filling of the EW period quotient and its finite ends. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

lemma regularSet_dense : Dense (regularSet (k := k) (m := m)) := by
  have hd : Dense {w : ClosedDisk | ‖w.val‖ < 1} := by
    apply (Subtype.dense_iff (s := {w : ℂ | ‖w‖ ≤ 1})).mpr
    have he : Subtype.val '' {w : ClosedDisk | ‖w.val‖ < 1} = Metric.ball (0 : ℂ) 1 := by
      ext z
      simp only [mem_image, mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
      exact ⟨fun ⟨w, hw, he⟩ => he ▸ hw,
        fun hz => ⟨⟨z, le_of_lt hz⟩, hz, rfl⟩⟩
    change {w : ℂ | ‖w‖ ≤ 1} ⊆ closure (Subtype.val '' {w : ClosedDisk | ‖w.val‖ < 1})
    rw [he, closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    intro z hz
    simpa using hz
  intro q
  induction q using Quotient.inductionOn with
  | h p =>
    have hc : Continuous (fun w : ClosedDisk => Quotient.mk (filledSetoid k m) (p.1,w)) :=
      continuous_quotient_mk'.comp (continuous_const.prodMk continuous_id)
    apply closure_mono (s := (fun w : ClosedDisk => Quotient.mk (filledSetoid k m) (p.1,w)) ''
      {w : ClosedDisk | ‖w.val‖ < 1}) ?_
      (mem_closure_image hc.continuousAt (hd p.2))
    rintro _ ⟨w, hw, rfl⟩ hp
    exact (ne_of_lt hw) (puncture_norm h.out hp)

/-- Added vertices are indexed by the roots of the Karcher denominator,
independently of the number of period copies. -/
def vertexEquiv : {q : FilledChain k m // q ∉ regularSet} ≃ {w // w ∈ punctureFinset k} where
  toFun q := ⟨(coordinate q.val).val,
    (mem_punctureFinset h.out).mpr (by simpa [regularSet] using q.property)⟩
  invFun w := ⟨Quotient.mk (filledSetoid k m)
    (0, ⟨w.val, le_of_eq (puncture_norm h.out ((mem_punctureFinset h.out).mp w.property))⟩),
    by simpa [regularSet, coordinate] using (mem_punctureFinset h.out).mp w.property⟩
  left_inv q := by
    rcases q with ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | h p =>
      apply Subtype.ext
      apply Quotient.sound
      exact ⟨rfl, Or.inl (by simpa [regularSet, coordinate] using hq)⟩
  right_inv _ := rfl

/-- Exactly `2k` points are added in the compact filling of any `m`-period quotient. -/
theorem vertex_card : Nat.card {q : FilledChain k m // q ∉ regularSet} = 2 * k := by
  rw [Nat.card_congr (vertexEquiv (k := k) (m := m)), Nat.card_eq_fintype_card,
    Fintype.card_coe, punctureFinset_card h.out]

/-- The original EW period quotient is the open, dense vertex complement in
the compact Hausdorff filled chain. -/
def periodQuotientHomeomorph (R : PaperHalfPeriodRealization k) :
    HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m ≃ₜ
      regularSet (k := k) (m := m) :=
  R.gluedDiskHomeomorph.symm.trans regularHomeomorph

end KsIndex.KarcherData.DiskCompactification
