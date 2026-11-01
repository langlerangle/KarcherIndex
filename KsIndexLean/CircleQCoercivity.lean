module

public import KsIndexLean.SIsometry

@[expose] public section


/-! Coercivity of the circle form in coefficient graph weights.
Physical trace norms require the separate Fourier and domain identifications. -/
noncomputable section
namespace KsIndex.CircleQ
/-- The minus-lattice weight is controlled by its energy and coefficient mass. -/
lemma tsum_minus_weight_le {u : ℤ → ℂ} (hu : MemDom u) :
    (∑' m : ℤ, |6 * (m : ℝ) + 4| * ‖convS u m‖ ^ 2) ≤
      (∑' m : ℤ, sigM m * ‖convS u m‖ ^ 2) + 2 * normSq u := by
  have hl2 := SIsometry.summable_convS_sq (summable_normSq hu.1)
  have hsig := summable_sigM_mul hu.2
  have h := hu.2.tsum_le_tsum (fun (m : ℤ) =>
    show |6 * (m : ℝ) + 4| * ‖convS u m‖ ^ 2 ≤
      sigM m * ‖convS u m‖ ^ 2 + 2 * ‖convS u m‖ ^ 2 by
      nlinarith [weight_le_sigM_add_two m, sq_nonneg ‖convS u m‖])
    (hsig.add (hl2.mul_left 2))
  rw [hsig.tsum_add (hl2.mul_left 2), tsum_mul_left,
    SIsometry.tsum_convS_sq_eq_normSq hu] at h
  exact h

/-- Sum of the two inhomogeneous half-order coefficient weights.
The sign-convolution isometry identifies both unweighted masses with `normSq u`. -/
def coefficientGraphNormSq (u : ℤ → ℂ) : ℝ :=
  (∑' n : ℤ, |6 * (n : ℝ) + 1| * ‖u n‖ ^ 2) + normSq u +
  ((∑' m : ℤ, |6 * (m : ℝ) + 4| * ‖convS u m‖ ^ 2) + normSq u)

/-- The coefficient graph estimate, valid also at zero and negative parameters.
The physical graph-norm comparison is not part of this theorem. -/
theorem coefficient_graph_coercivity (s : ℝ) {u : ℤ → ℂ} (hu : MemDom u) :
    min 1 (s ^ 2) * coefficientGraphNormSq u ≤
      Qform s u + 5 * (1 + s ^ 2) * normSq u := by
  have hp := tsum_weight_le hu
  have hm := tsum_minus_weight_le hu
  have hmass : 0 ≤ normSq u := tsum_nonneg (fun _ => sq_nonneg _)
  have hwp : 0 ≤ ∑' n : ℤ, |6 * (n : ℝ) + 1| * ‖u n‖ ^ 2 :=
    tsum_nonneg (fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
  have hwm : 0 ≤ ∑' m : ℤ, |6 * (m : ℝ) + 4| * ‖convS u m‖ ^ 2 :=
    tsum_nonneg (fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
  have ha := mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) (s ^ 2))
    (add_nonneg hwp hmass)
  have hb := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) (s ^ 2))
    (add_nonneg hwm hmass)
  have hc := mul_le_mul_of_nonneg_left hm (sq_nonneg s)
  unfold coefficientGraphNormSq Qform
  nlinarith [mul_nonneg (sq_nonneg s) hmass]
end KsIndex.CircleQ
