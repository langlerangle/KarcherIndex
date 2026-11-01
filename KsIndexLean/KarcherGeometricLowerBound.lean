module

public import KsIndexLean.KarcherGeometricInvariants
public import KsIndexLean.JacobiFamily

@[expose] public section


/-! A uniform lower bound for bounded-field nullity on the actual EW quotient. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization

/-- The three independent model Jacobi fields transport to the actual quotient.
No upper bound or special choice of period count is required. -/
theorem three_le_geometricNullity {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]
    (R : PaperHalfPeriodRealization k) : 3 ≤ R.geometricNullity (m := m) := by
  rw [R.geometricNullity_eq_model]
  exact JacobiFamily.three_le_nulSurface k m h.out

end KsIndex.KarcherData.PaperHalfPeriodRealization

#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.three_le_geometricNullity
