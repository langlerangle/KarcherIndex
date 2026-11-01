module

public import KsIndexLean.SphericalCoordinateInverse
public import Mathlib.Geometry.Manifold.Instances.Sphere

@[expose] public section


open Set Metric
open scoped ContDiff

noncomputable section
namespace KsIndex.Spherical

def north : Ambient := WithLp.toLp 2 ![0, 0, 1]
def scaledPlane (z : ℂ) : Ambient := WithLp.toLp 2 ![2 * z.re, 2 * z.im, 0]

lemma north_norm : ‖north‖ = 1 := by
  have h : ‖north‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [north, Fin.sum_univ_three]
  nlinarith [norm_nonneg north]

lemma scaledPlane_norm_sq (z : ℂ) : ‖scaledPlane z‖ ^ 2 = 4 * ‖z‖ ^ 2 := by
  have h : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [scaledPlane, Fin.sum_univ_three]
  nlinarith

lemma scaledPlane_orthogonal (z : ℂ) : scaledPlane z ∈ (ℝ ∙ north)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  simp [PiLp.inner_apply, Fin.sum_univ_three, north, scaledPlane]

lemma contDiff_scaledPlane : ContDiff ℝ ∞ scaledPlane := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun z : ℂ => 2 * z.re)
    exact contDiff_const.mul Complex.reCLM.contDiff
  · change ContDiff ℝ ∞ (fun z : ℂ => 2 * z.im)
    exact contDiff_const.mul Complex.imCLM.contDiff
  · exact contDiff_const

lemma stereoInvFunAux_scaledPlane (z : ℂ) :
    stereoInvFunAux north (scaledPlane z) = stereoPoint z := by
  have hd : 1 + ‖z‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  rw [stereoInvFunAux, scaledPlane_norm_sq]
  ext i
  fin_cases i <;> simp [scaledPlane, north, stereoPoint] <;> field_simp <;> ring

lemma stereoInvFun_scaledPlane (z : ℂ) :
    stereoInvFun north_norm ⟨scaledPlane z, scaledPlane_orthogonal z⟩ = sphereChart z := by
  apply Subtype.ext
  exact stereoInvFunAux_scaledPlane z

lemma contDiff_stereoPoint : ContDiff ℝ ∞ stereoPoint := by
  have h : stereoPoint = fun z => stereoInvFunAux north (scaledPlane z) :=
    funext fun z => (stereoInvFunAux_scaledPlane z).symm
  rw [h]
  exact (contDiff_stereoInvFunAux (v := north)).comp contDiff_scaledPlane

lemma stereoToFun_sphereChart (z : ℂ) :
    stereoToFun north (sphereChart z : Ambient) = ⟨scaledPlane z, scaledPlane_orthogonal z⟩ := by
  rw [← stereoInvFun_scaledPlane z]
  exact stereo_right_inv north_norm _

end KsIndex.Spherical
