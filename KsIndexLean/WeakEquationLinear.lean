module

public import KsIndexLean.WeakRepresentativeEquation

@[expose] public section


noncomputable section
open MeasureTheory TopologicalSpace
open scoped Distributions
namespace KsIndex.Weq

/-- Complex linear combinations preserve the bilinear weak equation. Local
integrability supplies the integral-additivity obligations explicitly. -/
theorem InteriorWeakEquation.linear_combination {Ω : Opens ℂ}
    {ux uy q vx vy r : ℂ → ℂ}
    (h : InteriorWeakEquation Ω ux uy q) (h' : InteriorWeakEquation Ω vx vy r)
    (hux : LocallyIntegrableOn ux Ω volume) (huy : LocallyIntegrableOn uy Ω volume)
    (hq : LocallyIntegrableOn q Ω volume) (hvx : LocallyIntegrableOn vx Ω volume)
    (hvy : LocallyIntegrableOn vy Ω volume) (hr : LocallyIntegrableOn r Ω volume)
    (c : ℂ) :
    InteriorWeakEquation Ω (fun z => ux z + c * vx z)
      (fun z => uy z + c * vy z) (fun z => q z + c * r z) := by
  intro ψ
  have ix := (derivTest ψ 1).integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℝ ℂ) hux
  have iy := (derivTest ψ Complex.I).integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℝ ℂ) huy
  have jx := (derivTest ψ 1).integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℝ ℂ) hvx
  have jy := (derivTest ψ Complex.I).integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℝ ℂ) hvy
  have iq := ψ.integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℝ ℂ) hq
  have ir := ψ.integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℝ ℂ) hr
  change Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z 1 * ux z) at ix
  change Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * uy z) at iy
  change Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z 1 * vx z) at jx
  change Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * vy z) at jy
  change Integrable (fun z => ψ z * q z) at iq
  change Integrable (fun z => ψ z * r z) at ir
  have hleft : (fun z => fderiv ℝ (ψ : ℂ → ℂ) z 1 * (ux z + c * vx z) +
      fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * (uy z + c * vy z)) =
      fun z => (fderiv ℝ (ψ : ℂ → ℂ) z 1 * ux z + fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * uy z) +
        c * (fderiv ℝ (ψ : ℂ → ℂ) z 1 * vx z + fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * vy z) := by
    funext z; ring
  have hright : (fun z => ψ z * (q z + c * r z)) =
      fun z => ψ z * q z + c * (ψ z * r z) := by funext z; ring
  have ixy : Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z 1 * ux z +
      fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * uy z) := ix.add iy
  have jxy : Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z 1 * vx z +
      fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * vy z) := jx.add jy
  rw [hleft, hright, integral_add ixy (jxy.const_mul c),
    integral_add iq (ir.const_mul c), integral_const_mul, integral_const_mul, h ψ, h' ψ]

end KsIndex.Weq
