module

public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section


open Set Metric

noncomputable section
namespace KsIndex.Spherical

abbrev Ambient := EuclideanSpace ℝ (Fin 3)
abbrev Sphere := Metric.sphere (0 : Ambient) 1

/-- Inverse stereographic projection in the paper's complex coordinate. -/
def stereoPoint (z : ℂ) : Ambient :=
  WithLp.toLp 2 ![2 * z.re / (1 + ‖z‖ ^ 2), 2 * z.im / (1 + ‖z‖ ^ 2),
    (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2)]

lemma stereoPoint_norm_sq (z : ℂ) : ‖stereoPoint z‖ ^ 2 = 1 := by
  have hd : 1 + ‖z‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hz : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_three]
  change (2 * z.re / (1 + ‖z‖ ^ 2)) ^ 2 + (2 * z.im / (1 + ‖z‖ ^ 2)) ^ 2 +
    ((‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2)) ^ 2 = 1
  field_simp
  nlinarith [sq_nonneg (‖z‖ ^ 2)]

def sphereChart (z : ℂ) : Sphere :=
  ⟨stereoPoint z, mem_sphere_zero_iff_norm.mpr (by
    have h := stereoPoint_norm_sq z
    nlinarith [norm_nonneg (stereoPoint z)])⟩

/-- Stereographic coordinate away from the north pole, totalized at the pole. -/
def stereoCoord (p : Ambient) : ℂ :=
  Complex.mk (p 0) (p 1) / ((1 - p 2 : ℝ) : ℂ)

lemma stereoCoord_stereoPoint (z : ℂ) : stereoCoord (stereoPoint z) = z := by
  have hd : 1 + ‖z‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  change Complex.mk (2 * z.re / (1 + ‖z‖ ^ 2)) (2 * z.im / (1 + ‖z‖ ^ 2)) /
    ((1 - (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) = z
  have he : 1 - (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2) = 2 / (1 + ‖z‖ ^ 2) := by
    field_simp
    ring
  have hn : Complex.mk (2 * z.re / (1 + ‖z‖ ^ 2)) (2 * z.im / (1 + ‖z‖ ^ 2)) =
      ((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z := by
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, add_zero] <;> ring
  have hc : ((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast div_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hd
  rw [he, hn]
  exact mul_div_cancel_left₀ z hc

lemma sphereChart_injective : Function.Injective sphereChart := by
  intro z w h
  have he := congrArg (fun p : Sphere => stereoCoord p.val) h
  simpa only [sphereChart, stereoCoord_stereoPoint] using he

end KsIndex.Spherical
