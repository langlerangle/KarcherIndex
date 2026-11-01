module

public import KsIndexLean.AlphaLowTotalm2
public import KsIndexLean.AlphaLowTotalm1
public import KsIndexLean.AlphaLowTotalp1
public import KsIndexLean.AlphaLowTotalp2
public import KsIndexLean.AlphaLowModeScalar

@[expose] public section

namespace KsIndex.AlphaRemarkTrial.LowProduction
open CircleQ AlphaResidual
theorem low_energy : (∑ n ∈ residualWindow 2, realResidual AlphaRemark.spectralUpper n^2/residualWeight n) ≤ (1/10000000 : ℝ) :=
  low_energy_of_linear_certificates m2_center_total m2_radius_total m1_center_total m1_radius_total p1_center_total p1_radius_total p2_center_total p2_radius_total
#print axioms low_energy
end KsIndex.AlphaRemarkTrial.LowProduction
