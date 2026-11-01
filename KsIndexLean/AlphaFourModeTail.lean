module

public import KsIndexLean.AlphaFourModeFiniteGram
public import KsIndexLean.ArcTailIntegral

@[expose] public section


/-! Analytic bounds for the omitted Fourier coefficients of the four-mode Gram matrix. -/
noncomputable section
namespace KsIndex.AlphaFourMode
open CircleQ Real ArcTailIntegral

def weight (n : ℤ) : ℝ := sigP n + 363/16

def kernel (i : Fin 4) (n : ℤ) : ℝ :=
  (-1)^(mode i-n) / (2*((mode i:ℝ)-(n:ℝ))+1)

lemma weight_pos (n : ℤ) : 0 < weight n := by
  have := sigP_ge_neg_three n
  dsimp [weight]
  linarith

lemma weight_ge_five_abs (n : ℤ) : 5*|(n:ℝ)| ≤ weight n := by
  have hfreq := abs_freqP_ge_one n
  have ha : 6*|(n:ℝ)| ≤ |6*(n:ℝ)+1|+1 := by
    have := abs_add_le (6*(n:ℝ)+1) (-1:ℝ)
    simpa [abs_mul] using this
  have hs : sigP n = |6*(n:ℝ)+1|-4/|6*(n:ℝ)+1| := by
    rw [sigP, ← sq_abs]
    field_simp
  have hi : 4/|6*(n:ℝ)+1| ≤ (4:ℝ) := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < |6*(n:ℝ)+1|)]
    linarith
  rw [weight, hs]
  nlinarith [abs_nonneg (n:ℝ)]

lemma kernel_abs_le {n : ℤ} (hn : (65:ℝ) ≤ |(n:ℝ)|) (i : Fin 4) :
    |kernel i n| ≤ 1/|(n:ℝ)| := by
  have hm : (-2:ℝ) ≤ (mode i:ℝ) ∧ (mode i:ℝ) ≤ 1 := by
    have hmi : (-2:ℤ) ≤ mode i ∧ mode i ≤ 1 := by
      have hi := i.isLt
      dsimp [mode]
      omega
    exact ⟨by exact_mod_cast hmi.1, by exact_mod_cast hmi.2⟩
  have hd : |(n:ℝ)| ≤ |2*((mode i:ℝ)-(n:ℝ))+1| := by
    rcases le_or_gt 0 (n:ℝ) with hp | hp
    · rw [abs_of_nonneg hp] at hn ⊢
      rw [abs_of_nonpos (by linarith)]
      linarith [hm.2]
    · rw [abs_of_neg hp] at hn ⊢
      rw [abs_of_nonneg (by linarith)]
      linarith [hm.1]
  have hz : |(-1:ℝ)^(mode i-n)| = 1 := by simp
  rw [kernel, abs_div, hz]
  exact one_div_le_one_div_of_le (by linarith) hd

/-- Cubic tail beyond the finite window on either half of the integer lattice. -/
lemma cubic_tail_64 : (∑' n : ℕ, 1/((n:ℝ)+65)^3) ≤ (1/8192:ℝ) := by
  have h := (antitone_cube (by norm_num : (0:ℝ)<64)).tsum_comp_add_le_integral 64
    (integrable_cube (by norm_num : (0:ℝ)<64))
    (fun x hx => show 0 ≤ cube x by
      have hx0 : 0 < x := lt_trans (by norm_num : (0:ℝ)<64) hx
      unfold cube
      positivity)
  rw [integral_cube (by norm_num)] at h
  norm_num only [Nat.cast_ofNat] at h
  simpa [cube, show ∀ n:ℕ, (n:ℝ)+64+1=(n:ℝ)+65 by intro n; ring] using h

def mixedKernel (a : Fin 4 → ℂ) (n : ℤ) : ℂ :=
  ∑ i, (kernel i n : ℂ) * a i

/-- Pointwise tail bound for every complex combination of the four rows. -/
lemma mixedKernel_tail_bound (a : Fin 4 → ℂ) {n : ℤ} (hn : (65:ℝ) ≤ |(n:ℝ)|) :
    ‖mixedKernel a n‖^2 / weight n ≤
      (4/5:ℝ) * (∑ i, ‖a i‖^2) / |(n:ℝ)|^3 := by
  have han : 0 < |(n:ℝ)| := by linarith
  have hb : ‖mixedKernel a n‖ ≤ (1/|(n:ℝ)|)*(∑ i, ‖a i‖) := by
    calc ‖mixedKernel a n‖ ≤ ∑ i, ‖(kernel i n:ℂ)*a i‖ := norm_sum_le _ _
      _ ≤ ∑ i, (1/|(n:ℝ)|)*‖a i‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (kernel_abs_le hn i) (norm_nonneg _)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hsq : (∑ i, ‖a i‖)^2 ≤ 4 * ∑ i, ‖a i‖^2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin 4 => ‖a i‖))
  calc ‖mixedKernel a n‖^2 / weight n
      ≤ ((1/|(n:ℝ)|)*(∑ i, ‖a i‖))^2 / weight n :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hb 2) (weight_pos n).le
    _ ≤ ((1/|(n:ℝ)|)*(∑ i, ‖a i‖))^2 / (5*|(n:ℝ)|) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (weight_ge_five_abs n)
    _ = (∑ i, ‖a i‖)^2 / (5*|(n:ℝ)|^3) := by field_simp
    _ ≤ (4 * ∑ i, ‖a i‖^2) / (5*|(n:ℝ)|^3) :=
        div_le_div_of_nonneg_right hsq (by positivity)
    _ = _ := by ring

end KsIndex.AlphaFourMode
