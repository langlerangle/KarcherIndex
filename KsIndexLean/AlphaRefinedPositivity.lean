module

public import KsIndexLean.AlphaRefinedGram

@[expose] public section


/-! Positivity on the full form domain at 27/20 and the resulting critical-phase bound. -/
noncomputable section
namespace KsIndex.AlphaRefined
open CircleQ SIsometry

lemma pairingEnergy_eq (a : Fin 4 → ℂ) (n : ℤ) :
    ‖AlphaFourMode.pairingKernel a n‖^2 / weight n = (2/Real.pi)^2 * gramEnergy a n := by
  simp only [AlphaFourMode.pairingKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs,
    gramEnergy]
  ring

lemma weightEnergy_summable {u : ℤ → ℂ} (hu : MemDom u) :
    Summable (fun n => weight n * ‖u n‖^2) := by
  simpa only [weight, add_mul] using
    (summable_sigP_mul hu.1).add ((summable_normSq hu.1).mul_left (2187/100))

lemma pairing_cauchy {u : ℤ → ℂ} (hu : MemDom u) (a : Fin 4 → ℂ) :
    ‖∑ i, a i * convS u (mode i)‖^2 ≤
      ((2/Real.pi)^2 * ∑' n, gramEnergy a n) * ∑' n, weight n * ‖u n‖^2 := by
  have hs : Summable (fun n => ‖AlphaFourMode.pairingKernel a n‖^2 / weight n) := by
    simpa only [pairingEnergy_eq] using (gramEnergy_summable a).mul_left ((2/Real.pi)^2)
  have hc := AlphaFourMode.weighted_complex_cauchy (AlphaFourMode.pairingKernel a) u weight
    weight_pos hs
    (weightEnergy_summable hu)
  rw [AlphaFourMode.pairing_tsum hu a] at hc
  simpa only [pairingEnergy_eq, tsum_mul_left] using hc


def scale (i : Fin 4) : ℝ := (729/400) * deficit i
lemma scale_pos (i : Fin 4) : 0 < scale i := by
  fin_cases i <;> norm_num [scale, deficit, AlphaFourMode.deficit]

def dualVector (z : Fin 4 → ℂ) (i : Fin 4) : ℂ := (scale i : ℂ) * star (z i)
def retainedEnergy (z : Fin 4 → ℂ) : ℝ := ∑ i, scale i * ‖z i‖^2

lemma retainedEnergy_nonneg (z : Fin 4 → ℂ) : 0 ≤ retainedEnergy z :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (scale_pos i).le (sq_nonneg _))

lemma dual_pairing (z : Fin 4 → ℂ) :
    (∑ i, dualVector z i * z i) = (retainedEnergy z : ℂ) := by
  unfold retainedEnergy
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have hn : ‖z i‖^2 = (z i).re^2 + (z i).im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [← Complex.ofReal_pow, hn]
  apply Complex.ext
  · simp [dualVector, Complex.mul_re, Complex.mul_im, -Complex.ofReal_pow]
    ring
  · simp [dualVector, Complex.mul_re, Complex.mul_im, -Complex.ofReal_pow]
    ring


lemma dual_diagonal (z : Fin 4 → ℂ) : diagonalEnergy (dualVector z) = retainedEnergy z := by
  unfold diagonalEnergy retainedEnergy
  apply Finset.sum_congr rfl
  intro i hi
  change ‖(scale i : ℂ) * star (z i)‖^2 / scale i = scale i * ‖z i‖^2
  rw [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp [(scale_pos i).ne']


def inputEnergy (u : ℤ → ℂ) : ℝ := ∑' n, weight n * ‖u n‖^2

lemma inputEnergy_pos {u : ℤ → ℂ} (hu : MemDom u) (hn : normSq u = 1) :
    0 < inputEnergy u := by
  have hl : (1887/100:ℝ) * normSq u ≤ inputEnergy u := by
    have h := ((summable_normSq hu.1).mul_left (1887/100)).tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_right
        (show (1887/100:ℝ) ≤ weight n by have := sigP_ge_neg_three n; unfold weight; linarith)
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
      (729/400:ℝ) * ∑ m ∈ AlphaFourMode.retainedModes, (12-sigM m)*‖convS u m‖^2 := by
  norm_num [retainedEnergy, scale, deficit, AlphaFourMode.deficit, mode, AlphaFourMode.mode,
    AlphaFourMode.retainedModes, sigM, Fin.sum_univ_succ]
  ring

lemma inputEnergy_eq {u : ℤ → ℂ} (hu : MemDom u) :
    inputEnergy u = (∑' n, sigP n * ‖u n‖^2) + (2187/100:ℝ)*normSq u := by
  simp only [inputEnergy, weight, add_mul]
  rw [(summable_sigP_mul hu.1).tsum_add ((summable_normSq hu.1).mul_left (2187/100)),
    tsum_mul_left]
  rfl

/-- Positivity on the entire normalized form domain at `27/20`. -/
theorem qform_twenty_seven_twentieths_pos {u : ℤ → ℂ} (hu : MemDom u) (hn : normSq u = 1) :
    0 < Qform (27/20) u := by
  have hret := retainedEnergy_lt_input hu hn
  rw [retainedEnergy_modes, inputEnergy_eq hu] at hret
  have hm := mul_le_mul_of_nonneg_left (AlphaFourMode.four_mode_momentum_bound hu)
    (show 0 ≤ (729/400:ℝ) by positivity)
  unfold Qform
  norm_num
  nlinarith

/-- Supplemental strict lower-bound certificate for the critical phase. -/
theorem gam_twenty_seven_twentieths_pos : 0 < gam (27/20) := by
  obtain ⟨u, hu, hn, he⟩ := exists_minimizer (show (0:ℝ) < 27/20 by positivity)
  rw [← he]
  exact qform_twenty_seven_twentieths_pos hu hn


/-- The critical phase exceeds `2/π * arctan (20/27)`. -/
theorem arc_bound_lt_alphaStar :
    2/Real.pi * Real.arctan (20/27) < Staircase.alphaStar := by
  have hs := Staircase.sstar_lt_of_gam_pos (show (0:ℝ)<27/20 by positivity)
    gam_twenty_seven_twentieths_pos
  have hi : (20/27:ℝ) < 1/Staircase.sstar := by
    have h := (one_div_lt_one_div (show (0:ℝ)<27/20 by positivity) Staircase.sstar_pos).mpr hs
    norm_num at h ⊢
    exact h
  exact mul_lt_mul_of_pos_left (Real.arctan_strictMono hi) (by positivity)

/-- The endpoint `2/π * arctan (20/27)` strictly exceeds `2/π * arctan (8/11)`. -/
theorem previous_endpoint_lt :
    2/Real.pi * Real.arctan (8/11) < 2/Real.pi * Real.arctan (20/27) :=
  mul_lt_mul_of_pos_left (Real.arctan_strictMono (by norm_num)) (by positivity)

/-- The supplemental rigorous interval, in exact transcendental form. -/
theorem alphaStar_mem_refined_interval :
    Staircase.alphaStar ∈ Set.Ioo (2/Real.pi * Real.arctan (20/27))
      (2/Real.pi * Real.arctan (6/7)) :=
  ⟨arc_bound_lt_alphaStar, AlphaStarBounds.alphaStar_lt_refined_arc_bound⟩

end KsIndex.AlphaRefined
