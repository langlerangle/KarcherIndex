module

public import KsIndexLean.AlphaLowProdDataF0R0
public import KsIndexLean.AlphaLowProdDataF0R1
public import KsIndexLean.AlphaLowProdDataF1R0
public import KsIndexLean.AlphaLowProdDataF1R1
public import KsIndexLean.AlphaTrialTableData

@[expose] public section


/-!
Two-level accessor over the generated integer streams, using blocks of 128 entries.

`B = 2161809` selects the first pair of streams; every other `B` selects the second.
Within either pair, `r = 0` selects the first stream and every other `r` the second.
A missing block or entry returns zero. The definition is total; these fallback
branches are not assertions of coefficient validity for arbitrary parameters.
-/
namespace KsIndex.PositiveEnergyAlphaLowProd

def t (B : ℤ) (r n : ℕ) : ℤ :=
  (((if B = 2161809 then (if r = 0 then s00 else s01)
    else (if r = 0 then s10 else s11))[n / 128]?.getD #[])[n % 128]?.getD 0)

end KsIndex.PositiveEnergyAlphaLowProd
