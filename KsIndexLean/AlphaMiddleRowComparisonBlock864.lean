module

public import KsIndexLean.AlphaMiddleRowComparisonData
public import KsIndexLean.AlphaMiddleArithmeticBlock864

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.MiddleComparisonBlock864
open MiddleInterval MiddleComparison
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def negative (i : Fin 32) : Bool := (864+i.val) % 2 != 0
def magnitude (i : Fin 32) : ℕ := (864+i.val)/2+3

theorem enclosure : ∀ i : Fin 32,
    MiddleBlock864.lo i ≤ rowLo (negative i) (magnitude i) (uLo (negative i)) (uHi (negative i)) ∧
      rowHi (negative i) (magnitude i) (uLo (negative i)) (uHi (negative i)) ≤ MiddleBlock864.hi i := by
  decide +kernel
end KsIndex.AlphaRemarkTrial.MiddleComparisonBlock864
#print axioms KsIndex.AlphaRemarkTrial.MiddleComparisonBlock864.enclosure
