module

public import KsIndexLean.KarcherCompactSurfaceAtlas

@[expose] public section


/-! Connectedness of the compactified EW quotient. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

instance : ConnectedSpace (FilledChain k m) := by
  let R := Classical.choice (exists_paperHalfPeriodRealization (k := k))
  let := R.connected
  have : ConnectedSpace (HeightLift.PeriodQuotient
      (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :=
    inferInstanceAs (ConnectedSpace (Quotient (HeightLift.periodSetoid
      (F := extendedEWMap h.out (reflectionBasepoint k) R.C) m)))
  have : ConnectedSpace (regularSet (k := k) (m := m)) :=
    (periodQuotientHomeomorph R).connectedSpace_iff.mp inferInstance
  have hd : DenseRange (fun q : regularSet (k := k) (m := m) => q.val) := by
    simpa only [DenseRange, Subtype.range_coe_subtype, Set.ofPred_mem_eq] using
      (regularSet_dense (k := k) (m := m))
  have : PreconnectedSpace (FilledChain k m) := hd.preconnectedSpace continuous_subtype_val
  exact ⟨⟨Quotient.mk (filledSetoid k m) (0, ⟨0, by simp⟩)⟩⟩

end KsIndex.KarcherData.DiskCompactification
