module
public import KsIndexLean.AlphaEnergy4096Decimal
@[expose] public section
namespace KsIndex.AlphaRemarkTrial.LowerAssembly
/-- The strict decimal bound obtained from the certified energy window of radius 4096. -/
theorem alphaStar_gt_4323617 : (4323617 / 10000000 : ℝ) < KsIndex.Staircase.alphaStar :=
  KsIndex.AlphaRemarkTrial.Energy4096Decimal.alphaStar_lower
end KsIndex.AlphaRemarkTrial.LowerAssembly
