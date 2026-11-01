module

public import KsIndexLean.AlphaRefinedTail
public import KsIndexLean.AlphaRefinedMatrix
public import KsIndexLean.AlphaFourModePairing

@[expose] public section


/-! Full integer Gram bound at the spectral parameter 27/20. -/
noncomputable section
namespace KsIndex.AlphaRefined
open CircleQ
abbrev mode := AlphaFourMode.mode
abbrev kernel := AlphaFourMode.kernel
abbrev mixedKernel := AlphaFourMode.mixedKernel
abbrev deficit := AlphaFourMode.deficit

def weight (n : ℤ) : ℝ := sigP n + 2187/100
def gramEnergy (a : Fin 4 → ℂ) (n : ℤ) : ℝ := ‖mixedKernel a n‖^2 / weight n

lemma weight_pos (n : ℤ) : 0 < weight n := by
  have := sigP_ge_neg_three n
  dsimp [weight]; linarith

lemma gramEnergy_nonneg (a : Fin 4 → ℂ) (n : ℤ) : 0 ≤ gramEnergy a n :=
  div_nonneg (sq_nonneg _) (weight_pos n).le

lemma energy_eq (a : Fin 4 → ℂ) (n : ℤ) :
    AlphaTailTask.energy (2187/100) a n = gramEnergy a n := rfl

lemma gramEnergy_summable (a : Fin 4 → ℂ) : Summable (gramEnergy a) :=
  (AlphaTailTask.full_sum_bound (2187/100) (by norm_num) 64 (by norm_num) a).1

lemma window_eq (f : ℤ → ℝ) :
    (∑ n ∈ Finset.range 129, f ((n:ℤ)-64)) = ∑ n ∈ Finset.Icc (-64:ℤ) 64, f n := by
  apply Finset.sum_bij (fun (n : ℕ) _ => (n:ℤ)-64)
  · intro n hn; simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Icc]; omega
  · intro a ha b hb h; omega
  · intro b hb; simp only [Finset.mem_Icc] at hb
    refine ⟨(b+64).toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]; omega
    · omega
  · intro n hn; rfl

lemma gramEnergy_tsum_le_finite (a : Fin 4 → ℂ) :
    (∑' n, gramEnergy a n) ≤ (∑ n ∈ Finset.Icc (-64:ℤ) 64, gramEnergy a n) +
      (1/23000:ℝ) * ∑ i, ‖a i‖^2 := by
  have h := (AlphaTailTask.full_sum_bound (2187/100) (by norm_num) 64 (by norm_num) a).2
  have ht : AlphaTailTask.tailAllowance 64 ≤ (1/23000:ℝ) := by
    norm_num [AlphaTailTask.tailAllowance]
  have hs : 0 ≤ ∑ i, ‖a i‖^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  change (∑' n, gramEnergy a n) ≤ (∑ n ∈ Finset.range 129, gramEnergy a ((n:ℤ)-64)) + _ at h
  rw [window_eq] at h
  linarith [mul_le_mul_of_nonneg_right ht hs]

lemma packet_kernel (i : Fin 4) (n : ℤ) : AlphaMatrixPacket.kernel i n = kernel i n := by
  unfold AlphaMatrixPacket.kernel AlphaMatrixPacket.mode kernel AlphaFourMode.kernel
    AlphaFourMode.mode
  push_cast
  rfl

lemma packet_weight (n : ℤ) : AlphaMatrixPacket.sigP n + 2187/100 = weight n := by
  have h := abs_freqP_ge_one n
  have hn : |6*(n : ℝ)+1| ≠ 0 := by linarith
  unfold AlphaMatrixPacket.sigP weight sigP
  rw [← sq_abs]
  field_simp

abbrev realMix := AlphaFourMode.realMix

def roundedForm (x : Fin 4 → ℝ) : ℝ := ∑ i, ∑ j, AlphaMatrixPacket.rounded i j * x i * x j

lemma finite_real_energy (x : Fin 4 → ℝ) :
    (∑ n ∈ Finset.Icc (-64:ℤ) 64, (realMix x n)^2 / weight n) =
      ∑ i, ∑ j, AlphaMatrixPacket.gram i j * x i * x j := by
  have he (n : ℤ) : (realMix x n)^2 / weight n =
      ∑ i, ∑ j, (kernel i n * kernel j n / weight n) * x i * x j := by
    simp only [realMix, AlphaFourMode.realMix, Fin.sum_univ_succ]; ring
  simp only [he, AlphaMatrixPacket.gram, packet_kernel, packet_weight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

lemma finiteGram_form_le (x : Fin 4 → ℝ) :
    (∑ i, ∑ j, AlphaMatrixPacket.gram i j * x i * x j) ≤
      roundedForm x + (4/1000000000:ℝ) * ∑ i, x i ^ 2 := by
  have h := AlphaFourMode.matrix_error_bound
    (fun i j => AlphaMatrixPacket.gram i j - AlphaMatrixPacket.rounded i j)
    (1/1000000000) (by positivity) AlphaMatrixPacket.gram_entry_enclosure x
  simp only [sub_mul, Finset.sum_sub_distrib] at h
  unfold roundedForm; linarith

lemma gramEnergy_parts (a : Fin 4 → ℂ) (n : ℤ) :
    gramEnergy a n = (realMix (fun i => (a i).re) n)^2 / weight n +
      (realMix (fun i => (a i).im) n)^2 / weight n := by
  unfold gramEnergy
  rw [Complex.sq_norm, Complex.normSq_apply]
  rw [(AlphaFourMode.mixedKernel_parts a n).1, (AlphaFourMode.mixedKernel_parts a n).2]
  ring

def gramUpper (a : Fin 4 → ℂ) : ℝ :=
  roundedForm (fun i => (a i).re) + roundedForm (fun i => (a i).im) +
    (1/23000 + 4/1000000000:ℝ) * ∑ i, ‖a i‖^2

lemma gramEnergy_le_upper (a : Fin 4 → ℂ) :
    (∑' n, gramEnergy a n) ≤ gramUpper a := by
  have ht := gramEnergy_tsum_le_finite a
  simp only [gramEnergy_parts, Finset.sum_add_distrib, finite_real_energy] at ht
  have hr := finiteGram_form_le (fun i => (a i).re)
  have hi := finiteGram_form_le (fun i => (a i).im)
  simp only [← gramEnergy_parts] at ht
  unfold gramUpper
  rw [AlphaFourMode.norm_sum_parts] at ht ⊢
  linarith

def diagonalEnergy (a : Fin 4 → ℂ) : ℝ :=
  ∑ i, ‖a i‖^2 / ((729/400:ℝ) * deficit i)

lemma real_certificate (x : Fin 4 → ℝ) :
    (1/50000:ℝ) * ∑ i, x i ^ 2 ≤
    (∑ i, x i ^ 2 / ((729/400:ℝ) * deficit i)) -
      (10000/24649:ℝ) * (roundedForm x +
        (1/23000 + 4/1000000000:ℝ) * ∑ i, x i ^ 2) := by
  have h := AlphaMatrixPacket.certificate_margin x
  convert h using 1
  · simp [roundedForm, AlphaMatrixPacket.certificate, AlphaMatrixPacket.rounded,
      AlphaMatrixPacket.deficit, deficit, AlphaFourMode.deficit, Fin.sum_univ_succ]
    ring

lemma complex_margin (a : Fin 4 → ℂ) :
    (1/50000:ℝ) * (∑ i, ‖a i‖^2) ≤
      diagonalEnergy a - (10000/24649:ℝ) * gramUpper a := by
  have hr := real_certificate (fun i => (a i).re)
  have hi := real_certificate (fun i => (a i).im)
  unfold diagonalEnergy gramUpper
  simp only [Complex.sq_norm, Complex.normSq_apply, ← pow_two, add_div, Finset.sum_add_distrib]
  linarith

theorem fourier_gram_strict {a : Fin 4 → ℂ} (ha : a ≠ 0) :
    (2/Real.pi)^2 * (∑' n, gramEnergy a n) < diagonalEnergy a := by
  have hs : 0 < ∑ i, ‖a i‖^2 := by
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra! h; exact ha (funext h)
    exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i, Finset.mem_univ _, sq_pos_of_pos
      (norm_pos_iff.mpr hi)⟩
  have hm := complex_margin a
  have hb := mul_le_mul_of_nonneg_left (gramEnergy_le_upper a) (show 0 ≤ (10000/24649:ℝ) by
    positivity)
  have hnon : 0 ≤ ∑' n, gramEnergy a n := tsum_nonneg (gramEnergy_nonneg a)
  have hp := mul_le_mul_of_nonneg_right AlphaFourMode.four_div_pi_sq_le hnon
  linarith

end KsIndex.AlphaRefined
