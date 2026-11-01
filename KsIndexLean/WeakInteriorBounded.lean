module

public import KsIndexLean.WeakLocalizedEquation
public import KsIndexLean.WeakBesselGain
public import KsIndexLean.WeakSobolevRepresentative
public import KsIndexLean.WeakH1Localization

@[expose] public section


/-! Local bounded representatives for an interior weak planar equation.
There is no condition on the outer boundary. -/
noncomputable section
open MeasureTheory TopologicalSpace
open scoped SchwartzMap Laplacian LineDeriv BoundedContinuousFunction

namespace KsIndex.Weq

lemma memLp_localizedSource {Ω : Opens ℂ} {u ux uy q : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ)))
    (hx : MemLp ux 2 (volume.restrict (Ω : Set ℂ)))
    (hy : MemLp uy 2 (volume.restrict (Ω : Set ℂ)))
    (hq : MemLp q 2 (volume.restrict (Ω : Set ℂ)))
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set ℂ)) : MemLp (localizedSource χ u ux uy q) 2 volume := by
  have hd (d : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ χ z d) :=
    (contDiff_infty_iff_fderiv.mp hχ).2.clm_apply contDiff_const
  have hdd (d : ℂ) : Continuous (fun z => fderiv ℝ (fun w => fderiv ℝ χ w d) z d) :=
    (((hd d).continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hdLp {f : ℂ → ℂ} (hf : MemLp f 2 (volume.restrict (Ω : Set ℂ))) (d : ℂ) :=
    Trace.memLp_continuous_mul_supported (hd d).continuous (hc.fderiv_apply (𝕜 := ℝ) d)
      ((tsupport_fderiv_apply_subset ℝ d).trans hs) hf
  have hddLp (d : ℂ) := Trace.memLp_continuous_mul_supported (hdd d)
    ((hc.fderiv_apply (𝕜 := ℝ) d).fderiv_apply (𝕜 := ℝ) d)
    ((tsupport_fderiv_apply_subset ℝ d).trans
      ((tsupport_fderiv_apply_subset ℝ d).trans hs)) hu
  have hqLp := Trace.memLp_continuous_mul_supported hχ.continuous hc hs hq
  have h := ((hqLp.neg.add ((hdLp hx 1).const_smul (2 : ℂ))).add
    ((hdLp hy Complex.I).const_smul (2 : ℂ))).add ((hddLp 1).add (hddLp Complex.I))
  convert h using 1
  ext z
  simp [localizedSource, add_smul, smul_eq_mul]

lemma toLp_distribution_apply {f : ℂ → ℂ} (hf : MemLp f 2 (volume : Measure ℂ))
    (φ : 𝓢(ℂ, ℂ)) : (hf.toLp : 𝓢'(ℂ, ℂ)) φ = ∫ z, φ z * f z := by
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with z hz
  simp [hz, smul_eq_mul]

lemma schwartz_laplacian_complex (φ : 𝓢(ℂ, ℂ)) (z : ℂ) :
    (Δ φ) z = fderiv ℝ (fun w => fderiv ℝ (φ : ℂ → ℂ) w 1) z 1 +
      fderiv ℝ (fun w => fderiv ℝ (φ : ℂ → ℂ) w Complex.I) z Complex.I := by
  have hd (ψ : 𝓢(ℂ, ℂ)) (d : ℂ) :
      ((∂_{d} ψ : 𝓢(ℂ, ℂ)) : ℂ → ℂ) = fun w => fderiv ℝ (ψ : ℂ → ℂ) w d := by
    funext w
    rw [SchwartzMap.lineDerivOp_apply,
      ((ψ.smooth ⊤).differentiable (by simp) w).lineDeriv_eq_fderiv]
  rw [SchwartzMap.laplacian_eq_sum Complex.orthonormalBasisOneI]
  simp only [Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI,
    Matrix.cons_val_zero, Matrix.cons_val_one, add_apply]
  change ((∂_{1} (∂_{1} φ) : 𝓢(ℂ, ℂ)) : ℂ → ℂ) z +
    ((∂_{Complex.I} (∂_{Complex.I} φ) : 𝓢(ℂ, ℂ)) : ℂ → ℂ) z = _
  simp_rw [hd]

/-- The localized interior weak equation is an actual distributional Laplace equation. -/
theorem localized_laplacian_distribution {Ω : Opens ℂ} {u ux uy q : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ)))
    (hux : MemLp ux 2 (volume.restrict (Ω : Set ℂ)))
    (huy : MemLp uy 2 (volume.restrict (Ω : Set ℂ)))
    (hq : MemLp q 2 (volume.restrict (Ω : Set ℂ)))
    (hx : TauCeti.HasWeakLineDerivOn volume Ω u ux 1)
    (hy : TauCeti.HasWeakLineDerivOn volume Ω u uy Complex.I)
    (heq : InteriorWeakEquation Ω ux uy q)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set ℂ)) :
    Δ ((Trace.memLp_continuous_mul_supported hχ.continuous hc hs hu).toLp : 𝓢'(ℂ, ℂ)) =
      ((memLp_localizedSource hu hux huy hq hχ hc hs).toLp : 𝓢'(ℂ, ℂ)) := by
  ext φ
  rw [TemperedDistribution.laplacian_apply_apply, toLp_distribution_apply,
    toLp_distribution_apply]
  simp_rw [schwartz_laplacian_complex]
  apply localized_laplacian_pairing hx hy _ heq hχ hc hs (φ.smooth ⊤)
  exact locallyIntegrableOn_of_locallyIntegrable_restrict (hq.locallyIntegrable (by norm_num))

/-- Concrete interior weak jets supply localized H² regularity. No boundary
condition is imposed on the edge of Ω. The localized H² conclusion supplies
the initial Sobolev regularity for the all-order bootstrap. -/
theorem memSobolev_two_cutoff {Ω : Opens ℂ} {u ux uy q : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ)))
    (hux : MemLp ux 2 (volume.restrict (Ω : Set ℂ)))
    (huy : MemLp uy 2 (volume.restrict (Ω : Set ℂ)))
    (hq : MemLp q 2 (volume.restrict (Ω : Set ℂ)))
    (hx : TauCeti.HasWeakLineDerivOn volume Ω u ux 1)
    (hy : TauCeti.HasWeakLineDerivOn volume Ω u uy Complex.I)
    (heq : InteriorWeakEquation Ω ux uy q)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set ℂ)) :
    TemperedDistribution.MemSobolev 2 2
      ((Trace.memLp_continuous_mul_supported hχ.continuous hc hs hu).toLp : 𝓢'(ℂ, ℂ)) := by
  let hf := Trace.memLp_continuous_mul_supported hχ.continuous hc hs hu
  let hr := memLp_localizedSource hu hux huy hq hχ hc hs
  have hd := localized_laplacian_distribution hu hux huy hq hx hy heq hχ hc hs
  have h₀ : TemperedDistribution.MemSobolev 0 2 (hf.toLp : 𝓢'(ℂ, ℂ)) :=
    TemperedDistribution.memSobolev_zero_iff.mpr ⟨hf.toLp, rfl⟩
  have hΔ : TemperedDistribution.MemSobolev 0 2 (Δ (hf.toLp : 𝓢'(ℂ, ℂ))) :=
    TemperedDistribution.memSobolev_zero_iff.mpr ⟨hr.toLp, hd⟩
  have hb : TemperedDistribution.MemSobolev 0 2
      (TemperedDistribution.besselPotential ℂ ℂ 2 (hf.toLp : 𝓢'(ℂ, ℂ))) := by
    rw [besselPotential_two_eq]
    simpa only [Complex.coe_smul] using
      h₀.sub (hΔ.smul (((2 * Real.pi) ^ 2)⁻¹ : ℝ))
  have h₂ : TemperedDistribution.MemSobolev 2 2 (hf.toLp : 𝓢'(ℂ, ℂ)) := by
    simpa only [add_zero] using TemperedDistribution.memSobolev_besselPotential_iff.mp hb
  exact h₂

/-- A local cutoff of an H¹ weak solution has a bounded continuous representative.
Only local tests and L² data are needed; no boundary condition is used. -/
theorem exists_boundedContinuous_cutoff {Ω : Opens ℂ} {u ux uy q : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ)))
    (hux : MemLp ux 2 (volume.restrict (Ω : Set ℂ)))
    (huy : MemLp uy 2 (volume.restrict (Ω : Set ℂ)))
    (hq : MemLp q 2 (volume.restrict (Ω : Set ℂ)))
    (hx : TauCeti.HasWeakLineDerivOn volume Ω u ux 1)
    (hy : TauCeti.HasWeakLineDerivOn volume Ω u uy Complex.I)
    (heq : InteriorWeakEquation Ω ux uy q)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set ℂ)) :
    ∃ g : ℂ →ᵇ ℂ, (fun z => χ z • u z) =ᵐ[volume] g := by
  let hf := Trace.memLp_continuous_mul_supported hχ.continuous hc hs hu
  have h₂ := memSobolev_two_cutoff hu hux huy hq hx hy heq hχ hc hs
  obtain ⟨g, hg⟩ := exists_boundedContinuous_ae_eq_of_memSobolev_two hf.toLp h₂
  exact ⟨g, hf.coeFn_toLp.symm.trans hg⟩

end KsIndex.Weq
