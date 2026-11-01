module

public import Palomar.CombinedSolution

/-!
# Proofs of the Karcher saddle tower index and critical-phase results

This module publicly re-exports the implementation in `Palomar.CombinedSolution`.
The comparator checks these five declarations in `KSPalomar.Intrinsic.Full`:

* `exists_intrinsic_index_nullity_m2`: the two-period index and nullity.
* `exists_intrinsic_staircase_k3`: the index staircase and resonance nullity.
* `unique_threshold`: existence and uniqueness of the spectral threshold.
* `decimal_bounds`: strict lower and upper bounds for its critical phase.
* `period_arithmetic`: floor values and nonresonance through period 2298.

All five use the same threshold definitions as the Challenge. The proofs and
geometric definitions are available in the imported implementation module.
-/
