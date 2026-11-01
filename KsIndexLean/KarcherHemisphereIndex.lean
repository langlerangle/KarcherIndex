module

public import KsIndexLean.KarcherNeumannIndex
public import KsIndexLean.HemisphereWeakIndex

@[expose] public section


/-! The compact Neumann test index of the geometric half period equals
the variational index on the actual single lower hemisphere. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

theorem halfPeriod_neumann_hemisphere_index (R : PaperHalfPeriodRealization k) (j : ℕ) :
    R.halfPeriodNeumannIndex j = Spherical.hemisphereWeakIndex k j true := by
  rw [R.halfPeriodNeumannIndex_eq_seamNat,
    Spherical.hemisphereWeakIndex_eq_seamNat h.out]

end KsIndex.KarcherData.PaperHalfPeriodRealization
