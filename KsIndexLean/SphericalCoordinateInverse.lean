module

public import KsIndexLean.SphericalHemisphere

@[expose] public section


open Set Metric

noncomputable section
namespace KsIndex.Spherical

lemma sphere_sum_sq (p : Sphere) : p.val 0 ^ 2 + p.val 1 ^ 2 + p.val 2 ^ 2 = 1 := by
  have hn : ‖p.val‖ = 1 := mem_sphere_zero_iff_norm.mp p.property
  have h := EuclideanSpace.real_norm_sq_eq p.val
  simpa [hn, Fin.sum_univ_three] using h.symm

lemma stereoCoord_norm_sq (p : Sphere) (hp : p.val 2 ≠ 1) :
    ‖stereoCoord p.val‖ ^ 2 = (1 + p.val 2) / (1 - p.val 2) := by
  have hd : 1 - p.val 2 ≠ 0 := sub_ne_zero.mpr hp.symm
  have hn : ‖Complex.mk (p.val 0) (p.val 1)‖ ^ 2 = p.val 0 ^ 2 + p.val 1 ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  simp only [stereoCoord, norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hn]
  field_simp
  nlinarith [sphere_sum_sq p]

lemma stereoPoint_stereoCoord (p : Sphere) (hp : p.val 2 ≠ 1) :
    stereoPoint (stereoCoord p.val) = p.val := by
  have hd : 1 - p.val 2 ≠ 0 := sub_ne_zero.mpr hp.symm
  have hr : (stereoCoord p.val).re = p.val 0 / (1 - p.val 2) := by
    simp only [stereoCoord, Complex.div_ofReal_re]
  have hi : (stereoCoord p.val).im = p.val 1 / (1 - p.val 2) := by
    simp only [stereoCoord, Complex.div_ofReal_im]
  ext i
  fin_cases i <;>
    simp only [stereoPoint, PiLp.toLp_apply, stereoCoord_norm_sq p hp, hr, hi] <;>
    field_simp <;> ring_nf <;> rfl

lemma range_sphereChart : Set.range sphereChart = {p : Sphere | p.val 2 ≠ 1} := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact stereoPoint_third_ne_one z
  · intro hp
    exact ⟨stereoCoord p.val, Subtype.ext (stereoPoint_stereoCoord p hp)⟩

end KsIndex.Spherical
