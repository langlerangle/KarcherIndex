module

public import KsIndexLean.ModeEnergyBounds

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace

/-- The conserved radial flux pairing for two solutions of the same equation. -/
def radialWronskian (f f' g g' : ℝ → ℂ) (r : ℝ) : ℂ :=
  g r * ((r : ℂ) * f' r) - f r * ((r : ℂ) * g' r)

lemma radialWronskian_hasDerivAt {f f' g g' : ℝ → ℂ} {q : ℂ} {r : ℝ}
    (hf : HasDerivAt f (f' r) r) (hg : HasDerivAt g (g' r) r)
    (hF : HasDerivAt (fun t : ℝ => (t : ℂ) * f' t) (q * f r) r)
    (hG : HasDerivAt (fun t : ℝ => (t : ℂ) * g' t) (q * g r) r) :
    HasDerivAt (radialWronskian f f' g g') 0 r := by
  convert (hg.mul hF).sub (hf.mul hG) using 1 <;> first | rfl | ring

lemma radialWronskian_eq_const {f f' g g' : ℝ → ℂ} {q : ℝ → ℂ}
    (hf : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' r) r)
    (hg : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt g (g' r) r)
    (hF : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t : ℝ => (t : ℂ) * f' t) (q r * f r) r)
    (hG : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t : ℝ => (t : ℂ) * g' t) (q r * g r) r) :
    ∀ r ∈ Ioo (0 : ℝ) 1, radialWronskian f f' g g' r = radialWronskian f f' g g' (1 / 2) := by
  have hd : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt (radialWronskian f f' g g') 0 r :=
    fun r hr => radialWronskian_hasDerivAt (hf r hr) (hg r hr) (hF r hr) (hG r hr)
  intro r hr
  exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv) hr (by norm_num)

/-- Bounded comparison solution and derivative control the conserved quantity
by the two weighted energies. This estimate has no centre regularity premise. -/
lemma radialWronskian_norm_sq_div_le {f f' g g' : ℝ → ℂ} {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hg : ‖g r‖ ≤ M) (hg' : ‖g' r‖ ≤ M) :
    ‖radialWronskian f f' g g' r‖ ^ 2 / r ≤
      2 * M ^ 2 * (r * ‖f' r‖ ^ 2 + r * ‖f r‖ ^ 2) := by
  have he : radialWronskian f f' g g' r = (r : ℂ) * (g r * f' r - f r * g' r) := by
    simp only [radialWronskian]
    ring
  have hn : ‖g r * f' r - f r * g' r‖ ≤ M * ‖f' r‖ + M * ‖f r‖ := by
    calc _ ≤ ‖g r * f' r‖ + ‖f r * g' r‖ := norm_sub_le _ _
      _ = ‖g r‖ * ‖f' r‖ + ‖f r‖ * ‖g' r‖ := by simp only [norm_mul]
      _ ≤ _ := by nlinarith [norm_nonneg (f r), norm_nonneg (f' r)]
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ M * ‖f' r‖ + M * ‖f r‖)).mpr hn
  have hbound : ‖g r * f' r - f r * g' r‖ ^ 2 ≤
      2 * M ^ 2 * (‖f' r‖ ^ 2 + ‖f r‖ ^ 2) := by
    nlinarith [sq_nonneg (M * ‖f' r‖ - M * ‖f r‖)]
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, mul_pow]
  have hc : r ^ 2 * ‖g r * f' r - f r * g' r‖ ^ 2 / r =
      r * ‖g r * f' r - f r * g' r‖ ^ 2 := by field_simp
  rw [hc]
  nlinarith [mul_le_mul_of_nonneg_left hbound hr.le]

end KsIndex.Trace
