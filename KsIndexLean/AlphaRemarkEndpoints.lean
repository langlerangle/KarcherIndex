module

public import KsIndexLean.ArctanPolynomialBounds
public import KsIndexLean.AlphaStarCertification
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section


/-! Exact phase comparisons for rational spectral test points bracketing the numerical remark.
The spectral sign hypotheses are not discharged in this module.
-/
noncomputable section
namespace KsIndex.AlphaRemark
open Real ArctanBounds

def spectralLower : ℝ := 12387574/10000000
def spectralUpper : ℝ := 12387581/10000000

lemma phase_lower_endpoint :
    (4323617/10000000 : ℝ) < 2/π * arctan (1/spectralUpper) := by
  rw [arctan_inv_reduction (show 1 ≤ spectralUpper by norm_num [spectralUpper])]
  have ha := arctan_le_upper (show 0 ≤ (spectralUpper-1)/(spectralUpper+1) by
    norm_num [spectralUpper])
  norm_num [upper, lower, spectralUpper] at ha
  rw [div_mul_eq_mul_div]
  apply (lt_div_iff₀ pi_pos).mpr
  have hp := pi_gt_d20
  norm_num [spectralUpper]
  nlinarith

lemma phase_upper_endpoint :
    2/π * arctan (1/spectralLower) < (4323619/10000000 : ℝ) := by
  rw [arctan_inv_reduction (show 1 ≤ spectralLower by norm_num [spectralLower])]
  have ha := lower_le_arctan (show 0 ≤ (spectralLower-1)/(spectralLower+1) by
    norm_num [spectralLower])
  norm_num [lower, spectralLower] at ha
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ pi_pos).mpr
  have hp := pi_lt_d20
  norm_num [spectralLower]
  nlinarith

/-- The two spectral sign hypotheses imply the exact decimal enclosure. -/
theorem decimal_enclosure_of_signs
    (hL : CircleQ.gam spectralLower < 0) (hU : 0 < CircleQ.gam spectralUpper) :
    (4323617/10000000 : ℝ) < Staircase.alphaStar ∧
      Staircase.alphaStar < (4323619/10000000 : ℝ) := by
  obtain ⟨hl,hu⟩ := Staircase.alphaStar_enclosure_of_signs
    (show 0 < spectralLower by norm_num [spectralLower])
    (show 0 < spectralUpper by norm_num [spectralUpper]) hL hU
  exact ⟨phase_lower_endpoint.trans hl, hu.trans phase_upper_endpoint⟩

end KsIndex.AlphaRemark
