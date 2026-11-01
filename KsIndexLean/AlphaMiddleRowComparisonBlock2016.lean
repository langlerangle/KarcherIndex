module

public import KsIndexLean.AlphaMiddleRowComparisonData
public import KsIndexLean.AlphaMiddleArithmeticBlock2016

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.MiddleComparisonBlock2016
open MiddleInterval MiddleComparison
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def negative (i : Fin 30) : Bool := (2016+i.val) % 2 != 0
def magnitude (i : Fin 30) : ℕ := (2016+i.val)/2+3

theorem enclosure : ∀ i : Fin 30,
    MiddleBlock2016.lo i ≤ rowLo (negative i) (magnitude i) (uLo (negative i)) (uHi (negative i)) ∧
      rowHi (negative i) (magnitude i) (uLo (negative i)) (uHi (negative i)) ≤ MiddleBlock2016.hi i := by
  decide +kernel
end KsIndex.AlphaRemarkTrial.MiddleComparisonBlock2016
#print axioms KsIndex.AlphaRemarkTrial.MiddleComparisonBlock2016.enclosure
