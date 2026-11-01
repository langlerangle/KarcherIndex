module

public import KsIndexLean.GeneralCapstoneConditional
public import KsIndexLean.NodeCCap

@[expose] public section


/-!
# Nullity of the two-period disk-chain model

The single-arc upper bound `nodeC_singleArcUpperBound` supplies the premise of
`nulSurface_eq_three_of_singleArc`. Its requirement `4 ≤ k` follows from the
middle-class conditions `2 ≤ j` and `j + 2 ≤ k`. The result holds for every
`k ≥ 3`; `KarcherGeometricCapstone` transports it to the actual EW quotient.
-/

noncomputable section
namespace KsIndex.NullityDecomp
open KsIndex.Surface

/-- The bounded Jacobi-field nullity of the two-period model is 3 for `k ≥ 3`. -/
theorem nulSurface_eq_three {k : ℕ} (hk : 3 ≤ k) : nulSurface k 2 = 3 :=
  nulSurface_eq_three_of_singleArc hk (fun _j hj2 hjk =>
    KsIndex.SingleArcReindex.nodeC_singleArcUpperBound (by omega) hj2 hjk)

end KsIndex.NullityDecomp
