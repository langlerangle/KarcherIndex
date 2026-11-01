module

public import KsIndexLean.JacobiFields

@[expose] public section


/-! Explicit boundary data for the k=3 translation Jacobi fields. These are
pointwise statements in the disk coordinate. Their transfer to weak traces and
Green identities is a separate obligation. -/
noncomputable section
namespace KsIndex.JacobiFields

lemma horizontal_formula (k : ℕ) (w : ℂ) :
    nu1 k w + Complex.I * nu2 k w =
      ((2 / (‖w‖ ^ (2 * k - 2) + 1) : ℝ) : ℂ) * w ^ (k - 1) := by
  apply Complex.ext <;>
    simp only [nu1, nu2, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring

lemma horizontal_radial (k : ℕ) {w : ℂ} (hw : ‖w‖ = 1) (r : ℝ) :
    nu1 k ((r : ℂ) * w) + Complex.I * nu2 k ((r : ℂ) * w) =
      ((2 * r ^ (k - 1) / (r ^ (2 * k - 2) + 1) : ℝ) : ℂ) * w ^ (k - 1) := by
  have hp : |r| ^ (2 * k - 2) = r ^ (2 * k - 2) := by
    rw [show 2 * k - 2 = 2 * (k - 1) by omega, pow_mul, pow_mul, sq_abs]
  rw [horizontal_formula]
  simp only [norm_mul, hw, mul_one, Complex.norm_real, Real.norm_eq_abs, hp, mul_pow]
  push_cast
  ring

/-- Every horizontal translation mode has zero outward derivative on the circle. -/
lemma horizontal_radial_derivative (k : ℕ) {w : ℂ} (hw : ‖w‖ = 1) :
    HasDerivAt (fun r : ℝ => nu1 k ((r : ℂ) * w) +
      Complex.I * nu2 k ((r : ℂ) * w)) (0 : ℂ) 1 := by
  have hd := (((hasDerivAt_id (1 : ℝ)).pow (k - 1)).const_mul 2).div
    (((hasDerivAt_id (1 : ℝ)).pow (2 * k - 2)).add_const 1)
    (by norm_num : (1 : ℝ) ^ (2 * k - 2) + 1 ≠ 0)
  have hd' : HasDerivAt (fun r : ℝ => 2 * r ^ (k - 1) / (r ^ (2 * k - 2) + 1)) 0 1 := by
    apply hd.congr_deriv
    simp only [Pi.pow_apply, id_eq, one_pow, mul_one]
    rw [show 2 * k - 2 = 2 * (k - 1) by omega]
    push_cast
    ring
  have hf : (fun r : ℝ => nu1 k ((r : ℂ) * w) + Complex.I * nu2 k ((r : ℂ) * w)) =
      (fun r : ℝ => ((2 * r ^ (k - 1) / (r ^ (2 * k - 2) + 1) : ℝ) : ℂ) * w ^ (k - 1)) :=
    funext (horizontal_radial k hw)
  rw [hf]
  simpa using hd'.ofReal_comp.mul_const (w ^ (k - 1))

lemma nu3_three_radial {w : ℂ} (hw : ‖w‖ = 1) (r : ℝ) :
    nu3 3 ((r : ℂ) * w) = (((r ^ 4 - 1) / (r ^ 4 + 1) : ℝ) : ℂ) := by
  have hp : |r| ^ 4 = r ^ 4 := by
    calc
      |r| ^ 4 = (|r| ^ 2) ^ 2 := by ring
      _ = (r ^ 2) ^ 2 := by rw [sq_abs]
      _ = r ^ 4 := by ring
  simp only [nu3, show 2 * 3 - 2 = 4 by decide, norm_mul, hw, mul_one,
    Complex.norm_real, Real.norm_eq_abs, hp]

/-- Outward radial derivative of the vertical translation field is 2 on the
unit circle. Its value there is zero, so this derivative is essential to the
nontrivial-phase obstruction. -/
lemma nu3_three_radial_derivative {w : ℂ} (hw : ‖w‖ = 1) :
    HasDerivAt (fun r : ℝ => nu3 3 ((r : ℂ) * w)) (2 : ℂ) 1 := by
  have hp := (hasDerivAt_id (1 : ℝ)).pow 4
  have hd := (hp.sub_const 1).div (hp.add_const 1) (by norm_num : (1 : ℝ) ^ 4 + 1 ≠ 0)
  have hd' : HasDerivAt (fun r : ℝ => (r ^ 4 - 1) / (r ^ 4 + 1)) 2 1 := by
    norm_num at hd
    exact hd
  have hf : (fun r : ℝ => nu3 3 ((r : ℂ) * w)) =
      (fun r : ℝ => (((r ^ 4 - 1) / (r ^ 4 + 1) : ℝ) : ℂ)) :=
    funext (nu3_three_radial hw)
  rw [hf]
  simpa using hd'.ofReal_comp

lemma nu3_three_boundary {w : ℂ} (hw : ‖w‖ = 1) : nu3 3 w = 0 := by
  simp [nu3, hw]

/-- The complex horizontal field has nonzero value at every boundary point. -/
lemma horizontal_three_boundary {w : ℂ} (hw : ‖w‖ = 1) :
    nu1 3 w + Complex.I * nu2 3 w = w ^ 2 := by
  simp only [nu1, nu2, hw, one_pow, show 3 - 1 = 2 by decide]
  have hr : 2 * (w ^ 2).re / (1 + 1) = (w ^ 2).re := by ring
  have hi : 2 * (w ^ 2).im / (1 + 1) = (w ^ 2).im := by ring
  rw [hr, hi, mul_comm Complex.I]
  exact Complex.re_add_im _

lemma horizontal_three_boundary_ne_zero {w : ℂ} (hw : ‖w‖ = 1) :
    nu1 3 w + Complex.I * nu2 3 w ≠ 0 := by
  rw [horizontal_three_boundary hw]
  apply pow_ne_zero
  intro hz
  simp [hz] at hw


lemma horizontal_three_formula (w : ℂ) :
    nu1 3 w + Complex.I * nu2 3 w =
      ((2 / (‖w‖ ^ 4 + 1) : ℝ) : ℂ) * w ^ 2 := by
  apply Complex.ext <;>
    simp only [nu1, nu2, show 3 - 1 = 2 by decide, show 2 * 3 - 2 = 4 by decide,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring

lemma horizontal_three_radial {w : ℂ} (hw : ‖w‖ = 1) (r : ℝ) :
    nu1 3 ((r : ℂ) * w) + Complex.I * nu2 3 ((r : ℂ) * w) =
      ((2 * r ^ 2 / (r ^ 4 + 1) : ℝ) : ℂ) * w ^ 2 := by
  have hp : |r| ^ 4 = r ^ 4 := by
    calc
      |r| ^ 4 = (|r| ^ 2) ^ 2 := by ring
      _ = (r ^ 2) ^ 2 := by rw [sq_abs]
      _ = r ^ 4 := by ring
  rw [horizontal_three_formula]
  simp only [norm_mul, hw, mul_one, Complex.norm_real, Real.norm_eq_abs, hp,
    mul_pow]
  push_cast
  ring

/-- The horizontal complex translation field has zero outward radial derivative. -/
lemma horizontal_three_radial_derivative {w : ℂ} (hw : ‖w‖ = 1) :
    HasDerivAt (fun r : ℝ => nu1 3 ((r : ℂ) * w) +
      Complex.I * nu2 3 ((r : ℂ) * w)) (0 : ℂ) 1 := by
  have hd := (((hasDerivAt_id (1 : ℝ)).pow 2).const_mul 2).div
    (((hasDerivAt_id (1 : ℝ)).pow 4).add_const 1)
    (by norm_num : (1 : ℝ) ^ 4 + 1 ≠ 0)
  have hd' : HasDerivAt (fun r : ℝ => 2 * r ^ 2 / (r ^ 4 + 1)) 0 1 := by
    norm_num at hd
    exact hd
  have hf : (fun r : ℝ => nu1 3 ((r : ℂ) * w) + Complex.I * nu2 3 ((r : ℂ) * w)) =
      (fun r : ℝ => ((2 * r ^ 2 / (r ^ 4 + 1) : ℝ) : ℂ) * w ^ 2) :=
    funext (horizontal_three_radial hw)
  rw [hf]
  simpa using hd'.ofReal_comp.mul_const (w ^ 2)

end KsIndex.JacobiFields

