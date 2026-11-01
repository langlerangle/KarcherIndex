module

public import KsIndexLean.NegSignCapstone

@[expose] public section


/-! Upper decimal bound on the staircase threshold from a certified negative
spectral sign. The spectral threshold lies above the lower test point, and the
phase transformation reverses the inequality. The complementary lower decimal
bound is proved in `AlphaRemarkLowerCertified`, a separate optional build root. -/

noncomputable section
namespace KsIndex.NegSignProd
open CircleQ Real

/-- The certified negative sign at the lower spectral test point gives
`α* < 0.4323619` through staircase monotonicity and a polynomial phase comparison. -/
theorem alphaStar_lt_upper_decimal :
    Staircase.alphaStar < (4323619 / 10000000 : ℝ) := by
  have hL : (0 : ℝ) < KsIndex.AlphaRemark.spectralLower := by
    rw [KsIndex.AlphaRemark.spectralLower]
    norm_num
  have hls := Staircase.lt_sstar_of_gam_neg hL gam_spectralLower_neg
  have h1 : Staircase.alphaStar <
      2 / π * arctan (1 / KsIndex.AlphaRemark.spectralLower) := by
    rw [Staircase.alphaStar]
    exact mul_lt_mul_of_pos_left
      (arctan_strictMono ((one_div_lt_one_div Staircase.sstar_pos hL).mpr hls))
      (by positivity)
  exact h1.trans KsIndex.AlphaRemark.phase_upper_endpoint

end KsIndex.NegSignProd
