module

public import KsIndexLean.SectorL2Unitary

@[expose] public section


/-! The paper's complementary-phase expression for the sector involution. -/

noncomputable section
namespace KsIndex.Sector

/-- The complementary phase multiplier is the negative adjoint multiplier. -/
lemma mulA_one_sub (α : ℝ) (u : Idx → ℂ) :
    mulA (1 - α) u = -mulAdag α u := by
  have h : (1 - α) * Real.pi = Real.pi - α * Real.pi := by ring
  simp only [mulA, mulAdag, h, Real.cos_pi_sub, Real.sin_pi_sub,
    Complex.ofReal_neg, neg_smul, neg_add_rev]
  abel

/-- Agreement with the expression `M_(1-α) P` in `rop_props`. -/
lemma rop_eq_mulA_one_sub_parity (α : ℝ) (u : Idx → ℂ) :
    rop α u = mulA (1 - α) (parity u) := by
  rw [mulA_one_sub]
  rfl

end KsIndex.Sector
