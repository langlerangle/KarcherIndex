module

public import KsIndexLean.SphericalReflection

@[expose] public section


noncomputable section
namespace KsIndex.Spherical

lemma stereoPoint_inverse_conj {z : ℂ} (hz : z ≠ 0) :
    stereoPoint ((starRingEnd ℂ z)⁻¹) = reflectAmbient (stereoPoint z) := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hr : ((starRingEnd ℂ z)⁻¹).re = z.re / ‖z‖ ^ 2 := by
    simp [Complex.inv_re, Complex.normSq_eq_norm_sq]
  have hi : ((starRingEnd ℂ z)⁻¹).im = z.im / ‖z‖ ^ 2 := by
    simp [Complex.inv_im, Complex.normSq_eq_norm_sq]
  ext i
  fin_cases i <;> simp [stereoPoint, reflectAmbient, hr, hi] <;> field_simp <;> ring

lemma southChart_inverse_conj {z : ℂ} (hz : z ≠ 0) :
    southChart z = sphereChart ((starRingEnd ℂ z)⁻¹) := by
  apply Subtype.ext
  exact (stereoPoint_inverse_conj hz).symm

end KsIndex.Spherical
