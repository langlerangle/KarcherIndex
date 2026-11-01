module

public import KsIndexLean.ProdDataF0R0
public import KsIndexLean.ProdDataF0R1
public import KsIndexLean.ProdDataF1R0
public import KsIndexLean.ProdDataF1R1
public import KsIndexLean.AlphaTrialTableData

@[expose] public section


/-! Two-level accessor over the generated streams. -/
namespace KsIndex.NegSignProd

def t (B : ℤ) (r n : ℕ) : ℤ :=
  (((if B = 2161809 then (if r = 0 then s00 else s01)
    else (if r = 0 then s10 else s11))[n / 128]?.getD #[])[n % 128]?.getD 0)

end KsIndex.NegSignProd
