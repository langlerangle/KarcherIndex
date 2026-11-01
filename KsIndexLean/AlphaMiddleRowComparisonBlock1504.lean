module

public import KsIndexLean.AlphaMiddleRowComparisonData
public import KsIndexLean.AlphaMiddleArithmeticBlock1504

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.MiddleComparisonBlock1504
open MiddleInterval MiddleComparison
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def negative (i : Fin 32) : Bool := (1504+i.val) % 2 != 0
def magnitude (i : Fin 32) : ℕ := (1504+i.val)/2+3

theorem enclosure : ∀ i : Fin 32,
    MiddleBlock1504.lo i ≤ rowLo (negative i) (magnitude i) (uLo (negative i)) (uHi (negative i)) ∧
      rowHi (negative i) (magnitude i) (uLo (negative i)) (uHi (negative i)) ≤ MiddleBlock1504.hi i := by
  decide +kernel
end KsIndex.AlphaRemarkTrial.MiddleComparisonBlock1504
#print axioms KsIndex.AlphaRemarkTrial.MiddleComparisonBlock1504.enclosure
