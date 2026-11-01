module

public import KsIndexLean.AlphaMiddleRowComparisonData
public import KsIndexLean.AlphaMiddleArithmeticBlock960

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.MiddleComparisonBlock960
open MiddleInterval MiddleComparison
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def negative (i : Fin 32) : Bool := (960+i.val) % 2 != 0
def magnitude (i : Fin 32) : ℕ := (960+i.val)/2+3

theorem enclosure : ∀ i : Fin 32,
    MiddleBlock960.lo i ≤ rowLo (negative i) (magnitude i) (uLo (negative i)) (uHi (negative i)) ∧
      rowHi (negative i) (magnitude i) (uLo (negative i)) (uHi (negative i)) ≤ MiddleBlock960.hi i := by
  decide +kernel
end KsIndex.AlphaRemarkTrial.MiddleComparisonBlock960
#print axioms KsIndex.AlphaRemarkTrial.MiddleComparisonBlock960.enclosure
