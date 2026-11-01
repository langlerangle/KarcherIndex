module

public import KsIndexLean.ProtoDataF0R0
public import KsIndexLean.ProtoDataF0R1
public import KsIndexLean.ProtoDataF1R0
public import KsIndexLean.ProtoDataF1R1
public import KsIndexLean.AlphaTrialTableData

@[expose] public section


/-! Two-level accessor over the generated streams. -/
namespace KsIndex.NegSignProto

def t (B : ℤ) (r n : ℕ) : ℤ :=
  (((if B = 2161809 then (if r = 0 then s00 else s01)
    else (if r = 0 then s10 else s11))[n / 32]?.getD #[])[n % 32]?.getD 0)

end KsIndex.NegSignProto
