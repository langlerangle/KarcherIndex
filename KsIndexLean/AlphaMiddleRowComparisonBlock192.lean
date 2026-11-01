module

public import KsIndexLean.AlphaMiddleRowComparisonData
public import KsIndexLean.AlphaMiddleArithmeticBlock192

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.MiddleComparisonBlock192
open MiddleInterval MiddleComparison
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def negative (i : Fin 32) : Bool := (192+i.val) % 2 != 0
def magnitude (i : Fin 32) : ℕ := (192+i.val)/2+3

theorem enclosure : ∀ i : Fin 32,
    MiddleBlock192.lo i ≤ rowLo (negative i) (magnitude i) (uLo (negative i)) (uHi (negative i)) ∧
      rowHi (negative i) (magnitude i) (uLo (negative i)) (uHi (negative i)) ≤ MiddleBlock192.hi i := by
  decide +kernel
end KsIndex.AlphaRemarkTrial.MiddleComparisonBlock192
#print axioms KsIndex.AlphaRemarkTrial.MiddleComparisonBlock192.enclosure
