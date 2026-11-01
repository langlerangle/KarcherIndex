module

public import KsIndexLean.SphericalMetric

@[expose] public section


open Set
open scoped ContDiff
noncomputable section
namespace KsIndex.Spherical

lemma stereoPoint_norm (z : ℂ) : ‖stereoPoint z‖ = 1 := by
  have h := stereoPoint_norm_sq z
  nlinarith [norm_nonneg (stereoPoint z)]

/-- Radial extension of the actual stereographic parametrization. -/
def radialStereo (p : ℝ × ℂ) : Ambient := p.1 • stereoPoint p.2

lemma radialStereo_norm (p : ℝ × ℂ) : ‖radialStereo p‖ = |p.1| := by
  simp [radialStereo, norm_smul, stereoPoint_norm]

lemma radialStereo_injOn : Set.InjOn radialStereo {p : ℝ × ℂ | 0 < p.1} := by
  intro p hp q hq he
  change 0 < p.1 at hp
  change 0 < q.1 at hq
  have hr := congrArg norm he
  simp only [radialStereo_norm, abs_of_pos hp, abs_of_pos hq] at hr
  apply Prod.ext hr
  have hS : stereoPoint p.2 = stereoPoint q.2 := by
    have ht : p.1 • stereoPoint p.2 = p.1 • stereoPoint q.2 := by
      simpa only [radialStereo, hr] using he
    exact (smul_right_injective _ (ne_of_gt hp)) ht
  exact sphereChart_injective (Subtype.ext hS)

lemma contDiff_radialStereo : ContDiff ℝ ∞ radialStereo :=
  contDiff_fst.smul (contDiff_stereoPoint.comp contDiff_snd)

/-- The stereographic differential is tangent to the actual unit sphere. -/
lemma stereoPoint_inner_differential (z v : ℂ) :
    inner ℝ (stereoPoint z) (stereoDifferential z v) = 0 := by
  have hh := (stereoPoint_line_deriv z v).norm_sq
  have he : (fun t : ℝ => ‖stereoPoint (z + t • v)‖ ^ 2) = fun _ => (1 : ℝ) := by
    funext t
    exact stereoPoint_norm_sq _
  rw [he] at hh
  have hu := hh.unique (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  simp only [zero_smul, add_zero] at hu
  linarith

lemma stereoPoint_inner_fderiv (z v : ℂ) :
    inner ℝ (stereoPoint z) (fderiv ℝ stereoPoint z v) = 0 := by
  rw [fderiv_stereoPoint_apply, stereoPoint_inner_differential]

/-- Differential of the radial parametrization, including the radial direction. -/
lemma fderiv_radialStereo_apply (p v : ℝ × ℂ) :
    fderiv ℝ radialStereo p v =
      v.1 • stereoPoint p.2 + p.1 • fderiv ℝ stereoPoint p.2 v.2 := by
  have hs := contDiff_stereoPoint.differentiable (by simp)
  have hh := (hasFDerivAt_fst (p := p)).smul
    (hs.differentiableAt.hasFDerivAt.comp p (hasFDerivAt_snd (p := p)))
  have he : ((Prod.fst : ℝ × ℂ → ℝ) • (stereoPoint ∘ (Prod.snd : ℝ × ℂ → ℂ))) = radialStereo := by
    funext q
    simp [radialStereo, Function.comp_def]
  rw [he] at hh
  simpa [Function.comp_def, add_comm] using
    congrArg (fun L : (ℝ × ℂ) →L[ℝ] Ambient => L v) hh.fderiv

/-- The radial direction is orthogonal to both chart directions. -/
lemma radialStereo_differential_norm_sq (p v : ℝ × ℂ) :
    ‖fderiv ℝ radialStereo p v‖ ^ 2 =
      v.1 ^ 2 + p.1 ^ 2 * (4 / (1 + ‖p.2‖ ^ 2) ^ 2) * ‖v.2‖ ^ 2 := by
  rw [fderiv_radialStereo_apply, norm_add_sq_real]
  simp only [inner_smul_left, inner_smul_right, stereoPoint_inner_fderiv,
    mul_zero, add_zero, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, stereoPoint_norm, mul_one, fderiv_stereoPoint_norm_sq]
  ring

end KsIndex.Spherical
