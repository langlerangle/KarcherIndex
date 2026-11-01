module

public import KsIndexLean.SeamChartOverlap

@[expose] public section


noncomputable section
namespace KsIndex.Trace

lemma fderiv_sigma_apply {z : ℂ} (hz : z ≠ 0) (d : ℂ) :
    fderiv ℝ KsIndex.Bracket.σ z d =
      -((starRingEnd ℂ) z)⁻¹ * (starRingEnd ℂ) d * ((starRingEnd ℂ) z)⁻¹ := by
  have hc : (starRingEnd ℂ) z ≠ 0 := by simpa using hz
  have h := (hasFDerivAt_inv' (𝕜 := ℝ) hc).comp z
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt
  have he : KsIndex.Bracket.σ = fun w => ((starRingEnd ℂ) w)⁻¹ := by
    funext w
    simp [KsIndex.Bracket.σ]
  change HasFDerivAt (fun w => ((starRingEnd ℂ) w)⁻¹) _ z at h
  rw [he, h.fderiv]
  simp [ContinuousLinearMap.mulLeftRight_apply, neg_mul]

lemma fderiv_sigma_radial {z : ℂ} (hz : z ≠ 0) :
    fderiv ℝ KsIndex.Bracket.σ z z = -KsIndex.Bracket.σ z := by
  rw [fderiv_sigma_apply hz]
  have hc : (starRingEnd ℂ) z ≠ 0 := by simpa using hz
  simp [KsIndex.Bracket.σ, hc]

lemma fderiv_sigma_rotation {z : ℂ} (hz : z ≠ 0) :
    fderiv ℝ KsIndex.Bracket.σ z (z * Complex.I) = KsIndex.Bracket.σ z * Complex.I := by
  rw [fderiv_sigma_apply hz]
  have hc : (starRingEnd ℂ) z ≠ 0 := by simpa using hz
  simp [KsIndex.Bracket.σ, map_mul, hc, mul_comm]

end KsIndex.Trace
