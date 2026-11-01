module

public import KsIndexLean.SphericalRadialGeometry
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section


open scoped ContDiff
noncomputable section
namespace KsIndex.Spherical

/-- Cartesian coordinates ordered as radius, real part, imaginary part. -/
def radialCoord : (Fin 3 → ℝ) →L[ℝ] (ℝ × ℂ) :=
  (ContinuousLinearMap.proj 0).prod
    ((Complex.ofRealCLM.comp (ContinuousLinearMap.proj 1)) +
      Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj 2)))

lemma radialCoord_apply (p : Fin 3 → ℝ) :
    radialCoord p = (p 0, (p 1 : ℂ) + Complex.I * (p 2 : ℂ)) := by
  simp [radialCoord]

/-- Radial stereographic map with Cartesian domain and codomain. -/
def radialCartesian (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  WithLp.ofLp (radialStereo (radialCoord p))

lemma fderiv_radialCartesian_apply (p v : Fin 3 → ℝ) :
    fderiv ℝ radialCartesian p v = WithLp.ofLp
      (v 0 • stereoPoint (radialCoord p).2 +
        p 0 • stereoDifferential (radialCoord p).2 (radialCoord v).2) := by
  have hr : HasFDerivAt radialStereo (fderiv ℝ radialStereo (radialCoord p))
      (radialCoord p) :=
    (contDiff_radialStereo.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hh := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).hasFDerivAt.comp p
    (hr.comp p radialCoord.hasFDerivAt)
  change HasFDerivAt radialCartesian _ p at hh
  rw [hh.fderiv]
  simp [fderiv_radialStereo_apply, fderiv_stereoPoint_apply, radialCoord_apply]
  rfl

lemma det_fderiv_radialCartesian (p : Fin 3 → ℝ) :
    (fderiv ℝ radialCartesian p).toLinearMap.det =
      -(p 0 ^ 2 * (4 / (1 + ‖(radialCoord p).2‖ ^ 2) ^ 2)) := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin 3)), Matrix.det_fin_three]
  simp [fderiv_radialCartesian_apply,
    radialCoord_apply, stereoDifferential, stereoPoint]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  field_simp
  ring

lemma abs_det_fderiv_radialCartesian (p : Fin 3 → ℝ) :
    |(fderiv ℝ radialCartesian p).toLinearMap.det| =
      p 0 ^ 2 * (4 / (1 + ‖(radialCoord p).2‖ ^ 2) ^ 2) := by
  rw [det_fderiv_radialCartesian, abs_neg, abs_of_nonneg (by positivity)]

lemma contDiff_radialCartesian : ContDiff ℝ ∞ radialCartesian :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff.comp
    (contDiff_radialStereo.comp radialCoord.contDiff)

lemma radialCoord_injective : Function.Injective radialCoord := by
  intro p q h
  have hr := congrArg Prod.fst h
  have hz := congrArg Prod.snd h
  have hx := congrArg Complex.re hz
  have hy := congrArg Complex.im hz
  funext i
  fin_cases i
  · simpa [radialCoord_apply] using hr
  · simpa [radialCoord_apply] using hx
  · simpa [radialCoord_apply] using hy

lemma radialCartesian_injOn : Set.InjOn radialCartesian {p | 0 < p 0} := by
  intro p hp q hq he
  apply radialCoord_injective
  apply radialStereo_injOn
  · simpa [radialCoord_apply] using hp
  · simpa [radialCoord_apply] using hq
  · exact WithLp.ofLp_injective 2 he

lemma radialCoord_surjective : Function.Surjective radialCoord := by
  rintro ⟨r, z⟩
  refine ⟨![r, z.re, z.im], ?_⟩
  simp only [radialCoord_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Prod.mk.injEq, true_and]
  apply Complex.ext <;> simp

end KsIndex.Spherical
