module

public import KsIndexLean.SphericalDifferential

@[expose] public section


noncomputable section
namespace KsIndex.Spherical

lemma stereoDifferential_norm_sq (z v : ℂ) :
    ‖stereoDifferential z v‖ ^ 2 = 4 / (1 + ‖z‖ ^ 2) ^ 2 * ‖v‖ ^ 2 := by
  have hd : 1 + ‖z‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_three]
  simp [stereoDifferential]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hd ⊢
  field_simp
  ring

/-- The pullback of the actual round metric has conformal factor 4/(1+|z|²)². -/
theorem fderiv_stereoPoint_norm_sq (z v : ℂ) :
    ‖fderiv ℝ stereoPoint z v‖ ^ 2 = 4 / (1 + ‖z‖ ^ 2) ^ 2 * ‖v‖ ^ 2 := by
  rw [fderiv_stereoPoint_apply, stereoDifferential_norm_sq]

theorem fderiv_stereoPoint_inner (z v w : ℂ) :
    inner ℝ (fderiv ℝ stereoPoint z v) (fderiv ℝ stereoPoint z w) =
      4 / (1 + ‖z‖ ^ 2) ^ 2 * inner ℝ v w := by
  have h := fderiv_stereoPoint_norm_sq z (v + w)
  rw [map_add, norm_add_sq_real, norm_add_sq_real,
    fderiv_stereoPoint_norm_sq, fderiv_stereoPoint_norm_sq] at h
  nlinarith

/-- Local area density computed from the actual chart's Gram matrix. -/
def stereoAreaDensity (z : ℂ) : ℝ :=
  Real.sqrt (inner ℝ (fderiv ℝ stereoPoint z 1) (fderiv ℝ stereoPoint z 1) *
    inner ℝ (fderiv ℝ stereoPoint z Complex.I) (fderiv ℝ stereoPoint z Complex.I) -
    (inner ℝ (fderiv ℝ stereoPoint z 1) (fderiv ℝ stereoPoint z Complex.I)) ^ 2)

lemma stereoAreaDensity_eq (z : ℂ) : stereoAreaDensity z = 4 / (1 + ‖z‖ ^ 2) ^ 2 := by
  unfold stereoAreaDensity
  rw [fderiv_stereoPoint_inner, fderiv_stereoPoint_inner, fderiv_stereoPoint_inner]
  have h11 : inner ℝ (1 : ℂ) 1 = 1 := by norm_num
  have hII : inner ℝ Complex.I Complex.I = 1 := by norm_num
  have h1I : inner ℝ (1 : ℂ) Complex.I = 0 := by norm_num
  rw [h11, hII, h1I]
  simp only [mul_one, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sub_zero, ← sq, Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (by positivity)

end KsIndex.Spherical
