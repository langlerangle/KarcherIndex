module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

@[expose] public section


/-! Bounded continuous representatives of planar H² functions. -/

noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap BoundedContinuousFunction

namespace KsIndex.Weq

theorem inverseFourier_pairing (v : Lp ℂ 1 (volume : Measure ℂ)) (φ : 𝓢(ℂ, ℂ)) :
    ∫ x, φ x • Real.Lp.fourierTransformInv v x =
      (𝓕⁻ (v : 𝓢'(ℂ, ℂ))) φ := by
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
  simp only [Real.Lp.fourierTransformInv_apply, SchwartzMap.fourierInv_coe]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))
    (L := -(innerₗ ℂ)) Real.continuous_fourierChar
    (show Continuous (fun p : ℂ × ℂ => -inner ℝ p.1 p.2) from continuous_inner.neg)
    φ.integrable (L1.integrable_coeFn v)
  have hflip : (-(innerₗ ℂ)).flip = -(innerₗ ℂ) := by
    ext x y
    simp [LinearMap.flip_apply, real_inner_comm]
  rw [hflip] at h
  exact h.symm

theorem exists_boundedContinuous_ae_eq_of_memSobolev_two
    (u : Lp ℂ 2 (volume : Measure ℂ))
    (hu : TemperedDistribution.MemSobolev 2 2 (u : 𝓢'(ℂ, ℂ))) :
    ∃ g : ℂ →ᵇ ℂ, (u : ℂ → ℂ) =ᵐ[volume] g := by
  obtain ⟨v, hv⟩ := hu.fourier_memL1 (by norm_num [Complex.finrank_real_complex])
  refine ⟨Real.Lp.fourierTransformInv v, ?_⟩
  have he : 𝓕⁻ (v : 𝓢'(ℂ, ℂ)) = (u : 𝓢'(ℂ, ℂ)) := by
    rw [← hv, fourierInv_fourier_eq]
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp u).locallyIntegrable (by norm_num))
    (Real.Lp.fourierTransformInv v).continuous.locallyIntegrable
  intro φ hφ hc
  let ψ : 𝓢(ℂ, ℂ) := (hc.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hφ)
  have h := inverseFourier_pairing v ψ
  rw [he, Lp.toTemperedDistribution_apply] at h
  change (∫ x, (φ x : ℂ) • Real.Lp.fourierTransformInv v x) =
    ∫ x, (φ x : ℂ) • u x at h
  simpa only [Complex.real_smul, smul_eq_mul] using h.symm

end KsIndex.Weq
