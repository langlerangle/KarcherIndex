module

public import KsIndexLean.AlphaFourModeMatrix

@[expose] public section


/-! Assembly of the real finite Gram form and the complex infinite energy. -/
noncomputable section
namespace KsIndex.AlphaFourMode

def realMix (x : Fin 4 → ℝ) (n : ℤ) : ℝ := ∑ i, kernel i n * x i

lemma realMix_sq (x : Fin 4 → ℝ) (n : ℤ) :
    (realMix x n)^2 / weight n =
      ∑ i, ∑ j, (kernel i n * kernel j n / weight n) * x i * x j := by
  simp only [realMix, Fin.sum_univ_succ]
  ring

lemma finiteGram_cast (i j : Fin 4) :
    (finiteGram i j : ℝ) = ∑ n ∈ Finset.range 129,
      kernel i ((n:ℤ)-64) * kernel j ((n:ℤ)-64) / weight ((n:ℤ)-64) := by
  unfold finiteGram
  push_cast
  simp only [rationalKernel_cast, rationalWeight_cast]

lemma finite_real_energy (x : Fin 4 → ℝ) :
    (∑ n ∈ Finset.range 129, (realMix x ((n:ℤ)-64))^2 / weight ((n:ℤ)-64)) =
      ∑ i, ∑ j, (finiteGram i j : ℝ) * x i * x j := by
  simp only [realMix_sq, finiteGram_cast, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

lemma mixedKernel_parts (a : Fin 4 → ℂ) (n : ℤ) :
    (mixedKernel a n).re = realMix (fun i => (a i).re) n ∧
    (mixedKernel a n).im = realMix (fun i => (a i).im) n := by
  simp [mixedKernel, realMix, Complex.mul_re, Complex.mul_im]

lemma gramEnergy_parts (a : Fin 4 → ℂ) (n : ℤ) :
    gramEnergy a n = (realMix (fun i => (a i).re) n)^2 / weight n +
      (realMix (fun i => (a i).im) n)^2 / weight n := by
  unfold gramEnergy
  rw [Complex.sq_norm, Complex.normSq_apply]
  rw [(mixedKernel_parts a n).1, (mixedKernel_parts a n).2]
  ring

lemma norm_sum_parts (a : Fin 4 → ℂ) :
    (∑ i, ‖a i‖^2) = (∑ i, (a i).re^2) + ∑ i, (a i).im^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, ← pow_two, Finset.sum_add_distrib]

def gramUpper (a : Fin 4 → ℂ) : ℝ :=
  roundedForm (fun i => (a i).re) + roundedForm (fun i => (a i).im) +
    (1/5120 + 4/10000000:ℝ) * ∑ i, ‖a i‖^2

lemma gramEnergy_le_upper (a : Fin 4 → ℂ) :
    (∑' n : ℤ, gramEnergy a n) ≤ gramUpper a := by
  have ht := gramEnergy_tsum_le_finite a
  simp only [gramEnergy_parts, Finset.sum_add_distrib, finite_real_energy] at ht
  have hr := finiteGram_form_le (fun i => (a i).re)
  have hi := finiteGram_form_le (fun i => (a i).im)
  simp only [← gramEnergy_parts] at ht
  rw [norm_sum_parts] at ht
  unfold gramUpper
  rw [norm_sum_parts]
  linarith

lemma gramUpper_nonneg (a : Fin 4 → ℂ) : 0 ≤ gramUpper a :=
  (tsum_nonneg (gramEnergy_nonneg a)).trans (gramEnergy_le_upper a)

def diagonalEnergy (a : Fin 4 → ℂ) : ℝ :=
  ∑ i, ‖a i‖^2 / ((121/64:ℝ) * deficit i)

lemma complexCertificate_matrix (a : Fin 4 → ℂ) :
    complexCertificate a = diagonalEnergy a - (10000/24649:ℝ) * gramUpper a := by
  unfold complexCertificate diagonalEnergy gramUpper
  rw [certificateForm_matrix, certificateForm_matrix, norm_sum_parts]
  simp only [Complex.sq_norm, Complex.normSq_apply, ← pow_two, add_div, Finset.sum_add_distrib]
  ring

theorem scaled_gram_strict {a : Fin 4 → ℂ} (ha : a ≠ 0) :
    (10000/24649:ℝ) * (∑' n : ℤ, gramEnergy a n) < diagonalEnergy a := by
  have hp := complexCertificate_pos ha
  rw [complexCertificate_matrix] at hp
  have hb := mul_le_mul_of_nonneg_left (gramEnergy_le_upper a)
    (show 0 ≤ (10000/24649:ℝ) by positivity)
  linarith

lemma four_div_pi_sq_le : (2/Real.pi)^2 ≤ (10000/24649:ℝ) := by
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos Real.pi_pos)]
  have h := Real.pi_gt_d2
  nlinarith [sq_nonneg (Real.pi - 157/50)]

theorem fourier_gram_strict {a : Fin 4 → ℂ} (ha : a ≠ 0) :
    (2/Real.pi)^2 * (∑' n : ℤ, gramEnergy a n) < diagonalEnergy a :=
  (mul_le_mul_of_nonneg_right four_div_pi_sq_le
    (tsum_nonneg (gramEnergy_nonneg a))).trans_lt (scaled_gram_strict ha)

end KsIndex.AlphaFourMode
