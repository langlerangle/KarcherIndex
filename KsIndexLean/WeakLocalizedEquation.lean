module

public import KsIndexLean.WeakComplexTest

@[expose] public section


/-! Localization of a weak divergence equation with complex, bilinear tests. -/
noncomputable section
open MeasureTheory TopologicalSpace
open scoped Distributions

namespace KsIndex.Weq
open WeakComplexTest

/-- The interior weak equation, with no boundary condition imposed. -/
def InteriorWeakEquation (Ω : Opens ℂ) (ux uy q : ℂ → ℂ) : Prop :=
  ∀ ψ : 𝓓(Ω, ℂ),
    (∫ z, fderiv ℝ (ψ : ℂ → ℂ) z 1 * ux z +
      fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * uy z) = ∫ z, ψ z * q z

theorem localized_divergence_pairing {Ω : Opens ℂ} {ux uy q : ℂ → ℂ}
    (hx : LocallyIntegrableOn ux Ω volume) (hy : LocallyIntegrableOn uy Ω volume)
    (hq : LocallyIntegrableOn q Ω volume) (heq : InteriorWeakEquation Ω ux uy q)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set ℂ)) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (∫ z, fderiv ℝ φ z 1 * (χ z • ux z) +
      fderiv ℝ φ z Complex.I * (χ z • uy z)) =
    ∫ z, φ z * (χ z • q z - fderiv ℝ χ z 1 • ux z -
      fderiv ℝ χ z Complex.I • uy z) := by
  let ψ := cutoffTest hχ hc hs hφ
  have hχd (d : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ χ z d) :=
    (contDiff_infty_iff_fderiv.mp hχ).2.clm_apply contDiff_const
  have hφd (d : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ φ z d) :=
    (contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const
  let A (d : ℂ) := cutoffTest hχ hc hs (hφd d)
  let B (d : ℂ) := cutoffTest (hχd d) (hc.fderiv_apply (𝕜 := ℝ) d)
    ((tsupport_fderiv_apply_subset ℝ d).trans hs) hφ
  have hAx := (A 1).integrable_bilin (ContinuousLinearMap.mul ℝ ℂ) hx
  have hAy := (A Complex.I).integrable_bilin (ContinuousLinearMap.mul ℝ ℂ) hy
  have hBx := (B 1).integrable_bilin (ContinuousLinearMap.mul ℝ ℂ) hx
  have hBy := (B Complex.I).integrable_bilin (ContinuousLinearMap.mul ℝ ℂ) hy
  have hQ := ψ.integrable_bilin (ContinuousLinearMap.mul ℝ ℂ) hq
  change Integrable (fun z => A 1 z * ux z) at hAx
  change Integrable (fun z => A Complex.I z * uy z) at hAy
  change Integrable (fun z => B 1 z * ux z) at hBx
  change Integrable (fun z => B Complex.I z * uy z) at hBy
  change Integrable (fun z => ψ z * q z) at hQ
  have hd (z d : ℂ) : fderiv ℝ (ψ : ℂ → ℂ) z d = B d z + A d z := by
    change fderiv ℝ (χ • φ) z d = _
    rw [((hχ.differentiable (by simp) z).hasFDerivAt.smul
      (hφ.differentiable (by simp) z).hasFDerivAt).fderiv]
    change χ z • fderiv ℝ φ z d + fderiv ℝ χ z d • φ z =
      fderiv ℝ χ z d • φ z + χ z • fderiv ℝ φ z d
    exact add_comm _ _
  have he := heq ψ
  simp_rw [hd, add_mul] at he
  have hsx : Integrable (fun z => B 1 z * ux z + A 1 z * ux z) := hBx.add hAx
  have hsy : Integrable (fun z => B Complex.I z * uy z + A Complex.I z * uy z) :=
    hBy.add hAy
  rw [integral_add hsx hsy, integral_add hBx hAx,
    integral_add hBy hAy] at he
  have hleft : (fun z => fderiv ℝ φ z 1 * (χ z • ux z) +
      fderiv ℝ φ z Complex.I * (χ z • uy z)) =
      fun z => A 1 z * ux z + A Complex.I z * uy z := by
    funext z
    change _ = (χ z • fderiv ℝ φ z 1) * ux z +
      (χ z • fderiv ℝ φ z Complex.I) * uy z
    simp only [Complex.real_smul]
    ring
  have hright : (fun z => φ z * (χ z • q z - fderiv ℝ χ z 1 • ux z -
      fderiv ℝ χ z Complex.I • uy z)) =
      fun z => ψ z * q z - B 1 z * ux z - B Complex.I z * uy z := by
    funext z
    change _ = (χ z • φ z) * q z - (fderiv ℝ χ z 1 • φ z) * ux z -
      (fderiv ℝ χ z Complex.I • φ z) * uy z
    simp only [Complex.real_smul]
    ring
  have hqx : Integrable (fun z => ψ z * q z - B 1 z * ux z) := hQ.sub hBx
  rw [hleft, hright, integral_add hAx hAy,
    integral_sub hqx hBy, integral_sub hQ hBx]
  linear_combination he

/-- Twice testing the localized weak derivative uses only the first weak jet. -/
theorem localized_second_pairing {Ω : Opens ℂ} {u v : ℂ → ℂ} {d : ℂ}
    (h : TauCeti.HasWeakLineDerivOn volume Ω u v d) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set ℂ)) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (∫ z, fderiv ℝ (fun w => fderiv ℝ φ w d) z d * (χ z • u z)) =
      -(∫ z, fderiv ℝ φ z d * (χ z • v z)) +
        ∫ z, φ z * (fderiv ℝ χ z d • v z +
          fderiv ℝ (fun w => fderiv ℝ χ w d) z d • u z) := by
  have hχd : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ χ z d) :=
    (contDiff_infty_iff_fderiv.mp hχ).2.clm_apply contDiff_const
  have hφd : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ φ z d) :=
    (contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const
  have he₁ := localized_integral_lineDeriv_mul h hχ hc hs hφd
  have he₂ := localized_integral_lineDeriv_mul h hχd
    (hc.fderiv_apply (𝕜 := ℝ) d) ((tsupport_fderiv_apply_subset ℝ d).trans hs) hφ
  simp_rw [(hφd.differentiable (by simp) _).lineDeriv_eq_fderiv] at he₁
  simp_rw [(hφ.differentiable (by simp) _).lineDeriv_eq_fderiv] at he₂
  let ψ₁ := cutoffTest hχ hc hs hφd
  let ψ₂ := cutoffTest hχd (hc.fderiv_apply (𝕜 := ℝ) d)
    ((tsupport_fderiv_apply_subset ℝ d).trans hs) hφd
  have h₁ := ψ₁.integrable_bilin (ContinuousLinearMap.mul ℝ ℂ) h.locallyIntegrableOn_deriv
  have h₂ := ψ₂.integrable_bilin (ContinuousLinearMap.mul ℝ ℂ) h.locallyIntegrableOn
  have hA : Integrable (fun z => fderiv ℝ φ z d * (χ z • v z)) := by
    convert h₁ using 1
    ext z
    change _ = (χ z • fderiv ℝ φ z d) * v z
    simp only [Complex.real_smul]
    ring
  have hB : Integrable (fun z => fderiv ℝ φ z d * (fderiv ℝ χ z d • u z)) := by
    convert h₂ using 1
    ext z
    change _ = (fderiv ℝ χ z d • fderiv ℝ φ z d) * u z
    simp only [Complex.real_smul]
    ring
  simp_rw [mul_add] at he₁
  rw [integral_add hA hB, he₂] at he₁
  linear_combination he₁

lemma integrable_cutoff_mul {Ω : Opens ℂ} {u : ℂ → ℂ}
    (hu : LocallyIntegrableOn u Ω volume) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set ℂ)) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : Integrable (fun z => φ z * (χ z • u z)) := by
  have h := (cutoffTest hχ hc hs hφ).integrable_bilin (ContinuousLinearMap.mul ℝ ℂ) hu
  convert h using 1
  ext z
  change _ = (χ z • φ z) * u z
  simp only [Complex.real_smul]
  ring

/-- The source in the localized Laplace equation. Its sign is fixed by
`∫ ∇φ·∇u = ∫ φq`, i.e. `Δu = -q`. -/
def localizedSource (χ : ℂ → ℝ) (u ux uy q : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(χ z • q z) + 2 * (fderiv ℝ χ z 1 • ux z) +
    2 * (fderiv ℝ χ z Complex.I • uy z) +
      (fderiv ℝ (fun w => fderiv ℝ χ w 1) z 1 +
        fderiv ℝ (fun w => fderiv ℝ χ w Complex.I) z Complex.I) • u z

theorem localized_laplacian_pairing {Ω : Opens ℂ} {u ux uy q : ℂ → ℂ}
    (hx : TauCeti.HasWeakLineDerivOn volume Ω u ux 1)
    (hy : TauCeti.HasWeakLineDerivOn volume Ω u uy Complex.I)
    (hq : LocallyIntegrableOn q Ω volume) (heq : InteriorWeakEquation Ω ux uy q)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set ℂ)) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (∫ z, (fderiv ℝ (fun w => fderiv ℝ φ w 1) z 1 +
      fderiv ℝ (fun w => fderiv ℝ φ w Complex.I) z Complex.I) * (χ z • u z)) =
      ∫ z, φ z * localizedSource χ u ux uy q z := by
  have hd {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      {f : ℂ → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (d : ℂ) :
      ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ f z d) :=
    (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const
  have hc' (d : ℂ) := hc.fderiv_apply (𝕜 := ℝ) d
  have hs' (d : ℂ) := (tsupport_fderiv_apply_subset ℝ d (f := χ)).trans hs
  have hχxx := integrable_cutoff_mul hx.locallyIntegrableOn
    (hd (hd hχ 1) 1) ((hc' 1).fderiv_apply (𝕜 := ℝ) 1)
    ((tsupport_fderiv_apply_subset ℝ 1).trans (hs' 1)) hφ
  have hχyy := integrable_cutoff_mul hx.locallyIntegrableOn
    (hd (hd hχ Complex.I) Complex.I) ((hc' Complex.I).fderiv_apply (𝕜 := ℝ) Complex.I)
    ((tsupport_fderiv_apply_subset ℝ Complex.I).trans (hs' Complex.I)) hφ
  have hχx := integrable_cutoff_mul hx.locallyIntegrableOn_deriv (hd hχ 1) (hc' 1) (hs' 1) hφ
  have hχy := integrable_cutoff_mul hy.locallyIntegrableOn_deriv
    (hd hχ Complex.I) (hc' Complex.I) (hs' Complex.I) hφ
  have hχq := integrable_cutoff_mul hq hχ hc hs hφ
  have hφx := integrable_cutoff_mul hx.locallyIntegrableOn_deriv hχ hc hs (hd hφ 1)
  have hφy := integrable_cutoff_mul hy.locallyIntegrableOn_deriv hχ hc hs (hd hφ Complex.I)
  have hφxx := integrable_cutoff_mul hx.locallyIntegrableOn hχ hc hs (hd (hd hφ 1) 1)
  have hφyy := integrable_cutoff_mul hx.locallyIntegrableOn hχ hc hs
    (hd (hd hφ Complex.I) Complex.I)
  have ex := localized_second_pairing hx hχ hc hs hφ
  have ey := localized_second_pairing hy hχ hc hs hφ
  have eqn := localized_divergence_pairing hx.locallyIntegrableOn_deriv
    hy.locallyIntegrableOn_deriv hq heq hχ hc hs hφ
  simp_rw [mul_add] at ex ey
  rw [integral_add hχx hχxx] at ex
  rw [integral_add hχy hχyy] at ey
  simp_rw [mul_sub] at eqn
  have hqx : Integrable (fun z => φ z * (χ z • q z) - φ z * (fderiv ℝ χ z 1 • ux z)) :=
    hχq.sub hχx
  rw [integral_add hφx hφy, integral_sub hqx hχy, integral_sub hχq hχx] at eqn
  have hr : (fun z => φ z * localizedSource χ u ux uy q z) = fun z =>
      -(φ z * (χ z • q z)) + (2 : ℂ) * (φ z * (fderiv ℝ χ z 1 • ux z)) +
      (2 : ℂ) * (φ z * (fderiv ℝ χ z Complex.I • uy z)) +
      (φ z * (fderiv ℝ (fun w => fderiv ℝ χ w 1) z 1 • u z) +
      φ z * (fderiv ℝ (fun w => fderiv ℝ χ w Complex.I) z Complex.I • u z)) := by
    funext z
    simp only [localizedSource, add_smul, mul_add]
    ring
  have hi₁ : Integrable (fun z => -(φ z * (χ z • q z)) +
      (2 : ℂ) * (φ z * (fderiv ℝ χ z 1 • ux z))) := hχq.neg.add (hχx.const_mul 2)
  have hi₂ : Integrable (fun z => -(φ z * (χ z • q z)) +
      (2 : ℂ) * (φ z * (fderiv ℝ χ z 1 • ux z)) +
      (2 : ℂ) * (φ z * (fderiv ℝ χ z Complex.I • uy z))) := hi₁.add (hχy.const_mul 2)
  have hi₃ : Integrable (fun z =>
      φ z * (fderiv ℝ (fun w => fderiv ℝ χ w 1) z 1 • u z) +
      φ z * (fderiv ℝ (fun w => fderiv ℝ χ w Complex.I) z Complex.I • u z)) :=
    hχxx.add hχyy
  have hnq : Integrable (fun z => -(φ z * (χ z • q z))) := hχq.neg
  simp_rw [add_mul]
  rw [hr, integral_add hφxx hφyy, integral_add hi₂ hi₃,
    integral_add hi₁ (hχy.const_mul 2), integral_add hnq (hχx.const_mul 2),
    integral_add hχxx hχyy, integral_neg, integral_const_mul, integral_const_mul]
  linear_combination ex + ey - eqn

end KsIndex.Weq
