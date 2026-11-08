module
public import KsIndexLean.AlphaEnergy4096Decimal
@[expose] public section
namespace KsIndex.NegSignProd
/-- The strict decimal bound obtained from the certified energy window of radius 4096. -/
theorem alphaStar_lt_upper_decimal : KsIndex.Staircase.alphaStar < (4323619 / 10000000 : ℝ) :=
  KsIndex.AlphaRemarkTrial.Energy4096Decimal.alphaStar_upper
end KsIndex.NegSignProd
