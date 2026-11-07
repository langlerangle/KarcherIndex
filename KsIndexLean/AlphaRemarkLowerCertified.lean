module
public import AlphaEnergy4096Decimal
@[expose] public section
namespace KsIndex.AlphaRemarkTrial.LowerAssembly
/-- The original strict decimal conclusion, using the certified4096 energy window. -/
theorem alphaStar_gt_4323617 : (4323617 / 10000000 : ℝ) < KsIndex.Staircase.alphaStar :=
  KsIndex.AlphaRemarkTrial.Energy4096Decimal.alphaStar_lower
end KsIndex.AlphaRemarkTrial.LowerAssembly
