module

public import KsIndexLean.AlphaFourModeDual

@[expose] public section


/-! Strict control of the retained output energy by the full input energy. -/
noncomputable section
namespace KsIndex.AlphaFourMode
open CircleQ SIsometry

def inputEnergy (u : ℤ → ℂ) : ℝ := ∑' n, weight n * ‖u n‖^2

lemma inputEnergy_pos {u : ℤ → ℂ} (hu : MemDom u) (hn : normSq u = 1) :
    0 < inputEnergy u := by
  have hl : (315/16:ℝ) * normSq u ≤ inputEnergy u := by
    have h := ((summable_normSq hu.1).mul_left (315/16)).tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_right
        (show (315/16:ℝ) ≤ weight n by have := sigP_ge_neg_three n; unfold weight; linarith)
        (sq_nonneg _)) (weightEnergy_summable hu)
    simpa only [tsum_mul_left, normSq, inputEnergy] using h
  rw [hn] at hl
  linarith

lemma retainedEnergy_lt_input {u : ℤ → ℂ} (hu : MemDom u) (hn : normSq u = 1) :
    retainedEnergy (fun i => convS u (mode i)) < inputEnergy u := by
  let z : Fin 4 → ℂ := fun i => convS u (mode i)
  have he := inputEnergy_pos hu hn
  have hl := retainedEnergy_nonneg z
  by_cases hz : dualVector z = 0
  · have hzero : retainedEnergy z = 0 := by
      have h := dual_diagonal z
      rw [hz] at h
      simpa [diagonalEnergy] using h.symm
    change retainedEnergy z < inputEnergy u
    rw [hzero]
    exact he
  · have hg := fourier_gram_strict hz
    rw [dual_diagonal] at hg
    have hc := pairing_cauchy hu (dualVector z)
    change ‖∑ i, dualVector z i * z i‖^2 ≤ _ at hc
    rw [dual_pairing, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hc
    change retainedEnergy z < inputEnergy u
    have hm := mul_lt_mul_of_pos_right hg he
    change _ < retainedEnergy z * inputEnergy u at hm
    have hL : 0 < retainedEnergy z := by
      have hG : 0 ≤ (2/Real.pi)^2 * ∑' n, gramEnergy (dualVector z) n :=
        mul_nonneg (sq_nonneg _) (tsum_nonneg (gramEnergy_nonneg _))
      linarith
    change _ ≤ _ * inputEnergy u at hc
    nlinarith

lemma retainedEnergy_modes (u : ℤ → ℂ) :
    retainedEnergy (fun i => convS u (mode i)) =
      (121/64:ℝ) * ∑ m ∈ retainedModes, (12-sigM m)*‖convS u m‖^2 := by
  norm_num [retainedEnergy, scale, deficit, mode, retainedModes, sigM, Fin.sum_univ_succ]
  ring

lemma inputEnergy_eq {u : ℤ → ℂ} (hu : MemDom u) :
    inputEnergy u = (∑' n, sigP n * ‖u n‖^2) + (363/16:ℝ)*normSq u := by
  simp only [inputEnergy, weight, add_mul]
  rw [(summable_sigP_mul hu.1).tsum_add ((summable_normSq hu.1).mul_left (363/16)),
    tsum_mul_left]
  rfl

/-- Positivity on the entire normalized form domain at the rational test point s=11/8. -/
theorem qform_eleven_eighths_pos {u : ℤ → ℂ} (hu : MemDom u) (hn : normSq u = 1) :
    0 < Qform (11/8) u := by
  have hret := retainedEnergy_lt_input hu hn
  rw [retainedEnergy_modes, inputEnergy_eq hu] at hret
  have hm := mul_le_mul_of_nonneg_left (four_mode_momentum_bound hu)
    (show 0 ≤ (121/64:ℝ) by positivity)
  unfold Qform
  norm_num
  nlinarith

/-- Supplemental strict lower-bound certificate for the critical phase. -/
theorem gam_eleven_eighths_pos : 0 < gam (11/8) := by
  obtain ⟨u, hu, hn, he⟩ := exists_minimizer (show (0:ℝ) < 11/8 by positivity)
  rw [← he]
  exact qform_eleven_eighths_pos hu hn

end KsIndex.AlphaFourMode
