module

public import KsIndexLean.WeakOpenExtension

@[expose] public section


/-! The concrete interior weak equation, interpreted locally on the zero extension.
There is deliberately no equation asserted across the boundary of the open set. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Distributions SchwartzMap Laplacian
namespace KsIndex.Weq

/-- A derivative of a test function is another test on the same open set. -/
def derivTest {Ω : Opens ℂ} (ψ : 𝓓(Ω, ℂ)) (d : ℂ) : 𝓓(Ω, ℂ) :=
  ⟨fun z => fderiv ℝ (ψ : ℂ → ℂ) z d,
    (contDiff_infty_iff_fderiv.mp ψ.contDiff).2.clm_apply contDiff_const,
    ψ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) d,
    (tsupport_fderiv_apply_subset ℝ d).trans ψ.tsupport_subset⟩

/-- Twice integrating the weak first derivatives against an interior test
recovers the scalar Laplace equation, with the sign fixed by the weak form. -/
theorem interior_laplacian_pairing {Ω : Opens ℂ} {u ux uy q : ℂ → ℂ}
    (hx : TauCeti.HasWeakLineDerivOn volume Ω u ux 1)
    (hy : TauCeti.HasWeakLineDerivOn volume Ω u uy Complex.I)
    (heq : InteriorWeakEquation Ω ux uy q) (ψ : 𝓓(Ω, ℂ)) :
    (∫ z, (fderiv ℝ (fun w => fderiv ℝ (ψ : ℂ → ℂ) w 1) z 1 +
      fderiv ℝ (fun w => fderiv ℝ (ψ : ℂ → ℂ) w Complex.I) z Complex.I) * u z) =
      -(∫ z, ψ z * q z) := by
  have hx' := WeakComplexTest.integral_lineDeriv_mul_eq_neg hx (derivTest ψ 1)
  have hy' := WeakComplexTest.integral_lineDeriv_mul_eq_neg hy (derivTest ψ Complex.I)
  simp_rw [((derivTest ψ 1).contDiff.differentiable (by simp) _).lineDeriv_eq_fderiv] at hx'
  simp_rw [((derivTest ψ Complex.I).contDiff.differentiable (by simp) _).lineDeriv_eq_fderiv] at hy'
  have hxx := (derivTest (derivTest ψ 1) 1).integrable_bilin
    (ContinuousLinearMap.mul ℝ ℂ) hx.locallyIntegrableOn
  have hyy := (derivTest (derivTest ψ Complex.I) Complex.I).integrable_bilin
    (ContinuousLinearMap.mul ℝ ℂ) hx.locallyIntegrableOn
  have hX := (derivTest ψ 1).integrable_bilin
    (ContinuousLinearMap.mul ℝ ℂ) hx.locallyIntegrableOn_deriv
  have hY := (derivTest ψ Complex.I).integrable_bilin
    (ContinuousLinearMap.mul ℝ ℂ) hy.locallyIntegrableOn_deriv
  simp only [derivTest, TestFunction.coe_mk, ContinuousLinearMap.mul_apply'] at hx' hy' hxx hyy hX hY
  simp_rw [add_mul]
  rw [integral_add hxx hyy, hx', hy']
  rw [← neg_add, ← integral_add hX hY, heq ψ]

/-- The interior weak equation produces exactly the distributional equation
consumed by the bootstrap. The zero extension introduces no boundary claim. -/
theorem localPotentialEquation_openDist {Ω : Opens ℂ} {u ux uy V : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ)))
    (hx : TauCeti.HasWeakLineDerivOn volume Ω u ux 1)
    (hy : TauCeti.HasWeakLineDerivOn volume Ω u uy Complex.I)
    (heq : InteriorWeakEquation Ω ux uy (fun z => V z * u z))
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    LocalPotentialEquation (Ω : Set ℂ) V (openDist u hu) := by
  intro χ hχ hc hs
  have ht := hc.hasTemperateGrowth hχ
  have htV : (fun z => χ z * V z).HasTemperateGrowth := (hc.mul_right (f' := V)).hasTemperateGrowth (hχ.mul hV)
  ext φ
  let Ψ : 𝓢(ℂ, ℂ) := SchwartzMap.smulLeftCLM ℂ χ φ
  have hΨ (z : ℂ) : Ψ z = χ z * φ z := by
    exact SchwartzMap.smulLeftCLM_apply_apply ht φ z
  let ψ : 𝓓(Ω, ℂ) := ⟨fun z => χ z * φ z, hχ.mul (φ.smooth ⊤),
    hc.mul_right, tsupport_mul_subset_left.trans hs⟩
  have hfun : (Ψ : ℂ → ℂ) = (ψ : ℂ → ℂ) := funext hΨ
  have hleft : (Δ (openDist u hu)) Ψ =
      ∫ z, (fderiv ℝ (fun w => fderiv ℝ (ψ : ℂ → ℂ) w 1) z 1 +
      fderiv ℝ (fun w => fderiv ℝ (ψ : ℂ → ℂ) w Complex.I) z Complex.I) * u z := by
    rw [TemperedDistribution.laplacian_apply_apply]
    change (openExtend u hu : 𝓢'(ℂ, ℂ)) (Δ Ψ) = _
    rw [Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [openExtend_ae u hu] with z hz
    rw [schwartz_laplacian_complex, hfun, hz]
    by_cases hzo : z ∈ (Ω : Set ℂ)
    · simp [Set.indicator_of_mem hzo, smul_eq_mul]
    · have hx0 := (derivTest (derivTest ψ 1) 1).zero_on_compl hzo
      have hy0 := (derivTest (derivTest ψ Complex.I) Complex.I).zero_on_compl hzo
      change fderiv ℝ (fun w => fderiv ℝ (ψ : ℂ → ℂ) w 1) z 1 = 0 at hx0
      change fderiv ℝ (fun w => fderiv ℝ (ψ : ℂ → ℂ) w Complex.I) z Complex.I = 0 at hy0
      simp [Set.indicator_of_notMem hzo, hx0, hy0]
  have hright : openDist u hu (SchwartzMap.smulLeftCLM ℂ (fun z => χ z * V z) φ) =
      ∫ z, ψ z * (V z * u z) := by
    change (openExtend u hu : 𝓢'(ℂ, ℂ)) _ = _
    rw [Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [openExtend_ae u hu] with z hz
    rw [SchwartzMap.smulLeftCLM_apply_apply htV, hz]
    by_cases hzo : z ∈ (Ω : Set ℂ)
    · simp only [Set.indicator_of_mem hzo, smul_eq_mul]
      change (χ z * V z) * φ z * u z = (χ z * φ z) * (V z * u z)
      ring
    · have hzχ : χ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzo (hs h))
      change _ = (χ z * φ z) * (V z * u z)
      simp [Set.indicator_of_notMem hzo, hzχ]
  change (Δ (openDist u hu)) Ψ =
    -(openDist u hu (SchwartzMap.smulLeftCLM ℂ (fun z => χ z * V z) φ))
  rw [hleft, hright]
  exact interior_laplacian_pairing hx hy heq ψ

end KsIndex.Weq
