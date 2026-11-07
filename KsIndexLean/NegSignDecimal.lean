module
public import AlphaEnergy4096Decimal
@[expose] public section
namespace KsIndex.NegSignProd
/-- The original strict decimal conclusion, using the certified4096 energy window. -/
theorem alphaStar_lt_upper_decimal : KsIndex.Staircase.alphaStar < (4323619 / 10000000 : ℝ) :=
  KsIndex.AlphaRemarkTrial.Energy4096Decimal.alphaStar_upper
end KsIndex.NegSignProd
