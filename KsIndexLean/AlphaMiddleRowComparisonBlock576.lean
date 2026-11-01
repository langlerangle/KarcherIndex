module

public import KsIndexLean.AlphaMiddleRowComparisonData
public import KsIndexLean.AlphaMiddleArithmeticBlock576

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.MiddleComparisonBlock576
open MiddleInterval MiddleComparison
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def negative (i : Fin 32) : Bool := (576+i.val) % 2 != 0
def magnitude (i : Fin 32) : ℕ := (576+i.val)/2+3

theorem enclosure : ∀ i : Fin 32,
    MiddleBlock576.lo i ≤ rowLo (negative i) (magnitude i) (uLo (negative i)) (uHi (negative i)) ∧
      rowHi (negative i) (magnitude i) (uLo (negative i)) (uHi (negative i)) ≤ MiddleBlock576.hi i := by
  decide +kernel
end KsIndex.AlphaRemarkTrial.MiddleComparisonBlock576
#print axioms KsIndex.AlphaRemarkTrial.MiddleComparisonBlock576.enclosure
