module

public import KsIndexLean.AlphaMiddleRowModel

@[expose] public section


/-! Numerical moment targets for row comparison only. These definitions do not
assert bounds on the analytic moment constants. -/
namespace KsIndex.AlphaRemarkTrial.MiddleComparison

def uLo (negative : Bool) : ℚ :=
  (if negative then 74848792232710618720219264367045728970428 else
    75435720375282880992999797257990978336632) / 10^40
def uHi (negative : Bool) : ℚ :=
  (if negative then 74848796918698190857446899454132167925740 else
    75435723763528590617612460575846781620200) / 10^40
end KsIndex.AlphaRemarkTrial.MiddleComparison
