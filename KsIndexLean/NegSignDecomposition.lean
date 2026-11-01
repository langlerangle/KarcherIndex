module

public import KsIndexLean.AlphaTrialTailEnergy

@[expose] public section


/-! Window-plus-four-tails decomposition of the circle form at the concrete
trial. Everything here is an exact identity or a one-sided comparison against
the gated tail enclosures; no numerical sign is asserted. -/

noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ PowerArc

/-! ### The symbols are dominated by their linear weights. -/

lemma freqP_ne_zero (n : ℤ) : (6 * (n : ℝ) + 1) ≠ 0 := by
  have h1 : ((6 * n + 1 : ℤ) : ℝ) = 6 * (n : ℝ) + 1 := by push_cast; ring
  rw [← h1]
  exact_mod_cast (show (6 * n + 1 : ℤ) ≠ 0 by omega)

lemma freqM_ne_zero (m : ℤ) : (6 * (m : ℝ) + 4) ≠ 0 := by
  have h1 : ((6 * m + 4 : ℤ) : ℝ) = 6 * (m : ℝ) + 4 := by push_cast; ring
  rw [← h1]
  exact_mod_cast (show (6 * m + 4 : ℤ) ≠ 0 by omega)

lemma sigP_le_abs (n : ℤ) : sigP n ≤ |6 * (n : ℝ) + 1| := by
  have hpos : 0 < |6 * (n : ℝ) + 1| := abs_pos.mpr (freqP_ne_zero n)
  rw [CircleQ.sigP, div_le_iff₀ hpos]
  nlinarith [sq_abs (6 * (n : ℝ) + 1), sq_nonneg (6 * (n : ℝ) + 1)]

lemma sigM_le_abs (m : ℤ) : sigM m ≤ |6 * (m : ℝ) + 4| := by
  have hpos : 0 < |6 * (m : ℝ) + 4| := abs_pos.mpr (freqM_ne_zero m)
  rw [CircleQ.sigM, div_le_iff₀ hpos]
  nlinarith [sq_abs (6 * (m : ℝ) + 4), sq_nonneg (6 * (m : ℝ) + 4)]

/-! ### Splitting a summable ℤ-series into a window and two tails. -/

lemma tsum_int_window_split {f : ℤ → ℝ} (hf : Summable f) (M : ℕ) :
    ∑' n : ℤ, f n =
      ((∑ n ∈ Finset.range (M + 1), f n)
        + ∑ n ∈ Finset.range M, f (-((n : ℤ) + 1)))
      + ((∑' k : ℕ, f ((M : ℤ) + 1 + k)) + ∑' k : ℕ, f (-((M : ℤ) + 1) - k)) := by
  have hpos : Summable (fun n : ℕ => f n) :=
    hf.comp_injective (fun a b h => by exact_mod_cast h)
  have hneg : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    hf.comp_injective (fun a b h => by omega)
  have h1 : (∑' n : ℕ, (f n + f (-((n : ℤ) + 1)))) = ∑' n : ℤ, f n :=
    tsum_nat_add_neg_add_one hf
  rw [hpos.tsum_add hneg] at h1
  have h2 := hpos.sum_add_tsum_nat_add (M + 1)
  have h3 := hneg.sum_add_tsum_nat_add M
  have e2 : (∑' k : ℕ, f ((k + (M + 1) : ℕ))) = ∑' k : ℕ, f ((M : ℤ) + 1 + k) := by
    apply tsum_congr
    intro k
    congr 1
    push_cast
    ring
  have e3 : (∑' k : ℕ, f (-(((k + M : ℕ) : ℤ) + 1))) =
      ∑' k : ℕ, f (-((M : ℤ) + 1) - k) := by
    apply tsum_congr
    intro k
    congr 1
    push_cast
    ring
  rw [e2] at h2
  rw [e3] at h3
  linarith

/-- The two-range window equals the symmetric integer interval sum. -/
lemma window_sum_eq_Icc (f : ℤ → ℝ) (M : ℕ) :
    ((∑ n ∈ Finset.range (M + 1), f n)
      + ∑ n ∈ Finset.range M, f (-((n : ℤ) + 1))) =
      ∑ n ∈ Finset.Icc (-(M : ℤ)) M, f n := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hIcc : Finset.Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ) =
        insert (-((M + 1 : ℕ) : ℤ))
          (insert (((M + 1 : ℕ) : ℤ)) (Finset.Icc (-(M : ℤ)) (M : ℤ))) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hn1 : (-((M + 1 : ℕ) : ℤ)) ∉
        insert (((M + 1 : ℕ) : ℤ)) (Finset.Icc (-(M : ℤ)) (M : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hn2 : (((M + 1 : ℕ) : ℤ)) ∉ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    rw [Finset.sum_range_succ (fun n : ℕ => f (-((n : ℤ) + 1))) M,
      Finset.sum_range_succ (fun n : ℕ => f ((n : ℤ))) (M + 1),
      hIcc, Finset.sum_insert hn1, Finset.sum_insert hn2, ← ih]
    push_cast
    ring

/-! ### Linear-weight tail majorants are summable. -/

lemma summable_linear_sample_sq_pos (K : ℤ) (hK : 7 ≤ K) (c : ℝ) :
    Summable (fun k : ℕ => (6 * (k : ℝ) + c) * sample (K + 2 * k) ^ 2) := by
  have hr : ∀ i, (1 : ℝ) ≤ ((K + shift i : ℤ) : ℝ) := by
    intro i
    have hi := (shift_bounds i).1
    exact_mod_cast (show (1 : ℤ) ≤ K + shift i by omega)
  have hexp : ∀ k : ℕ, (6 * (k : ℝ) + c) * sample (K + 2 * k) ^ 2 =
      ∑ i, ∑ j, (6 * (k : ℝ) + c) *
        (tailScale i * g (exponent i) (((K + shift i : ℤ) : ℝ) + 2 * k)) *
        (tailScale j * g (exponent j) (((K + shift j : ℤ) : ℝ) + 2 * k)) := by
    intro k
    rw [sample_positive_tail, pow_two, Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  apply Summable.congr _ (fun k => (hexp k).symm)
  exact summable_sum (fun i _ => summable_sum (fun j _ =>
    scaled_mixed_linear_summable (tailScale i) (tailScale j)
      (exponent_pos i) (exponent_pos j) (hr i) (hr j)))

lemma summable_linear_sample_sq_neg (K : ℤ) (hK : 7 ≤ K) (c : ℝ) :
    Summable (fun k : ℕ => (6 * (k : ℝ) + c) * sample (-K - 2 * k) ^ 2) := by
  have hr : ∀ i, (1 : ℝ) ≤ ((K - shift i : ℤ) : ℝ) := by
    intro i
    have hi := (shift_bounds i).2
    exact_mod_cast (show (1 : ℤ) ≤ K - shift i by omega)
  have hexp : ∀ k : ℕ, (6 * (k : ℝ) + c) * sample (-K - 2 * k) ^ 2 =
      ∑ i, ∑ j, (6 * (k : ℝ) + c) *
        (tailScale i * g (exponent i) (((K - shift i : ℤ) : ℝ) + 2 * k)) *
        (tailScale j * g (exponent j) (((K - shift j : ℤ) : ℝ) + 2 * k)) := by
    intro k
    rw [sample_negative_tail, pow_two, Finset.sum_mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  apply Summable.congr _ (fun k => (hexp k).symm)
  exact summable_sum (fun i _ => summable_sum (fun j _ =>
    scaled_mixed_linear_summable (tailScale i) (tailScale j)
      (exponent_pos i) (exponent_pos j) (hr i) (hr j)))

/-! ### Generic tail comparison against the gated enclosures. -/

lemma tsum_tail_le_pos {σ : ℕ → ℝ} {c : ℝ} (K : ℤ) (hK : 7 ≤ K)
    (hσ0 : ∀ k, 0 ≤ σ k) (hσ : ∀ k, σ k ≤ 6 * (k : ℝ) + c) :
    (∑' k : ℕ, σ k * sample (K + 2 * k) ^ 2) ≤
      tailLeading (fun i => ((K + shift i : ℤ) : ℝ)) +
        tailError (fun i => ((K + shift i : ℤ) : ℝ)) c := by
  have hmaj := summable_linear_sample_sq_pos K hK c
  have hpt : ∀ k : ℕ, σ k * sample (K + 2 * k) ^ 2 ≤
      (6 * (k : ℝ) + c) * sample (K + 2 * k) ^ 2 := fun k =>
    mul_le_mul_of_nonneg_right (hσ k) (sq_nonneg _)
  have hnn : ∀ k : ℕ, 0 ≤ σ k * sample (K + 2 * k) ^ 2 := fun k =>
    mul_nonneg (hσ0 k) (sq_nonneg _)
  have hsum := hmaj.of_nonneg_of_le hnn hpt
  have hle := hsum.tsum_le_tsum hpt hmaj
  have hb := positive_sample_tail_bound K hK c
  have hub := (abs_le.mp hb).2
  linarith

lemma tsum_tail_le_neg {σ : ℕ → ℝ} {c : ℝ} (K : ℤ) (hK : 7 ≤ K)
    (hσ0 : ∀ k, 0 ≤ σ k) (hσ : ∀ k, σ k ≤ 6 * (k : ℝ) + c) :
    (∑' k : ℕ, σ k * sample (-K - 2 * k) ^ 2) ≤
      tailLeading (fun i => ((K - shift i : ℤ) : ℝ)) +
        tailError (fun i => ((K - shift i : ℤ) : ℝ)) c := by
  have hmaj := summable_linear_sample_sq_neg K hK c
  have hpt : ∀ k : ℕ, σ k * sample (-K - 2 * k) ^ 2 ≤
      (6 * (k : ℝ) + c) * sample (-K - 2 * k) ^ 2 := fun k =>
    mul_le_mul_of_nonneg_right (hσ k) (sq_nonneg _)
  have hnn : ∀ k : ℕ, 0 ≤ σ k * sample (-K - 2 * k) ^ 2 := fun k =>
    mul_nonneg (hσ0 k) (sq_nonneg _)
  have hsum := hmaj.of_nonneg_of_le hnn hpt
  have hle := hsum.tsum_le_tsum hpt hmaj
  have hb := negative_sample_tail_bound K hK c
  have hub := (abs_le.mp hb).2
  linarith

/-! ### The main window-plus-four-tails upper bound. -/

/-- `Qform s trial` is at most the symmetric finite window plus the four gated
tail enclosures, with Astra's four `(K, c)` parameter pairs. -/
theorem qform_trial_le_window_add_tails (s : ℝ) (M : ℕ) (hM : 3 ≤ M) :
    Qform s trial ≤
      (((∑ n ∈ Finset.Icc (-(M : ℤ)) M, sigP n * sample (2 * n) ^ 2)
        + s ^ 2 * ∑ m ∈ Finset.Icc (-(M : ℤ)) M, sigM m * sample (2 * m + 1) ^ 2)
      + ((tailLeading (fun i => ((2 * M + 2 + shift i : ℤ) : ℝ))
          + tailError (fun i => ((2 * M + 2 + shift i : ℤ) : ℝ)) (6 * M + 7))
        + (tailLeading (fun i => ((2 * M + 2 - shift i : ℤ) : ℝ))
          + tailError (fun i => ((2 * M + 2 - shift i : ℤ) : ℝ)) (6 * M + 5))))
      + s ^ 2 *
        ((tailLeading (fun i => ((2 * M + 3 + shift i : ℤ) : ℝ))
          + tailError (fun i => ((2 * M + 3 + shift i : ℤ) : ℝ)) (6 * M + 10))
        + (tailLeading (fun i => ((2 * M + 1 - shift i : ℤ) : ℝ))
          + tailError (fun i => ((2 * M + 1 - shift i : ℤ) : ℝ)) (6 * M + 2))) := by
  classical
  -- Real-valued sample forms of the two coefficient series.
  have htrial : ∀ n : ℤ, ‖trial n‖ ^ 2 = sample (2 * n) ^ 2 := by
    intro n
    rw [trial_eq_sample, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hconv : ∀ m : ℤ, ‖convS trial m‖ ^ 2 = sample (2 * m + 1) ^ 2 := by
    intro m
    rw [convS_eq_sample, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  set fP : ℤ → ℝ := fun n => sigP n * sample (2 * n) ^ 2 with hfP
  set fM : ℤ → ℝ := fun m => sigM m * sample (2 * m + 1) ^ 2 with hfM
  have hPsum : Summable fP := by
    apply (summable_sigP_mul trial_memDom.1).congr
    intro n
    rw [hfP]
    dsimp only
    rw [htrial]
  have hMsum : Summable fM := by
    apply (summable_sigM_mul trial_memDom.2).congr
    intro m
    rw [hfM]
    dsimp only
    rw [hconv]
  have hPeq : (∑' n : ℤ, sigP n * ‖trial n‖ ^ 2) = ∑' n : ℤ, fP n := by
    apply tsum_congr
    intro n
    rw [htrial n]
  have hMeq : (∑' m : ℤ, sigM m * ‖convS trial m‖ ^ 2) = ∑' m : ℤ, fM m := by
    apply tsum_congr
    intro m
    rw [hconv m]
  -- Split both series.
  have hPsplit := tsum_int_window_split hPsum M
  have hMsplit := tsum_int_window_split hMsum M
  rw [window_sum_eq_Icc] at hPsplit hMsplit
  -- P⁺ tail.
  have hPpos : (∑' k : ℕ, fP ((M : ℤ) + 1 + k)) ≤
      tailLeading (fun i => ((2 * M + 2 + shift i : ℤ) : ℝ))
        + tailError (fun i => ((2 * M + 2 + shift i : ℤ) : ℝ)) (6 * M + 7) := by
    have he : (∑' k : ℕ, fP ((M : ℤ) + 1 + k)) =
        ∑' k : ℕ, sigP ((M : ℤ) + 1 + k) * sample ((2 * M + 2 : ℤ) + 2 * k) ^ 2 := by
      apply tsum_congr
      intro k
      rw [hfP]
      dsimp only
      rw [show (2 * ((M : ℤ) + 1 + k)) = (2 * M + 2 : ℤ) + 2 * k by push_cast; ring]
    rw [he]
    apply tsum_tail_le_pos (2 * M + 2 : ℤ) (by omega)
    · intro k
      have := sigP_ge_of_ne_zero (show ((M : ℤ) + 1 + k) ≠ 0 by omega)
      linarith
    · intro k
      calc sigP ((M : ℤ) + 1 + k) ≤ |6 * (((M : ℤ) + 1 + k : ℤ) : ℝ) + 1| :=
            sigP_le_abs _
        _ = 6 * (k : ℝ) + (6 * M + 7) := by
            rw [abs_of_nonneg (by push_cast; positivity)]
            push_cast
            ring
  -- P⁻ tail.
  have hPneg : (∑' k : ℕ, fP (-((M : ℤ) + 1) - k)) ≤
      tailLeading (fun i => ((2 * M + 2 - shift i : ℤ) : ℝ))
        + tailError (fun i => ((2 * M + 2 - shift i : ℤ) : ℝ)) (6 * M + 5) := by
    have he : (∑' k : ℕ, fP (-((M : ℤ) + 1) - k)) =
        ∑' k : ℕ, sigP (-((M : ℤ) + 1) - k) * sample (-(2 * M + 2 : ℤ) - 2 * k) ^ 2 := by
      apply tsum_congr
      intro k
      rw [hfP]
      dsimp only
      rw [show (2 * (-((M : ℤ) + 1) - k)) = -(2 * M + 2 : ℤ) - 2 * k by push_cast; ring]
    rw [he]
    apply tsum_tail_le_neg (2 * M + 2 : ℤ) (by omega)
    · intro k
      have := sigP_ge_of_ne_zero (show (-((M : ℤ) + 1) - k) ≠ 0 by omega)
      linarith
    · intro k
      calc sigP (-((M : ℤ) + 1) - k) ≤ |6 * ((-((M : ℤ) + 1) - k : ℤ) : ℝ) + 1| :=
            sigP_le_abs _
        _ = 6 * (k : ℝ) + (6 * M + 5) := by
            rw [show (6 * ((-((M : ℤ) + 1) - k : ℤ) : ℝ) + 1) =
              -(6 * (k : ℝ) + (6 * M + 5)) by push_cast; ring, abs_neg,
              abs_of_nonneg (by positivity)]
  -- M⁺ tail.
  have hMpos : (∑' k : ℕ, fM ((M : ℤ) + 1 + k)) ≤
      tailLeading (fun i => ((2 * M + 3 + shift i : ℤ) : ℝ))
        + tailError (fun i => ((2 * M + 3 + shift i : ℤ) : ℝ)) (6 * M + 10) := by
    have he : (∑' k : ℕ, fM ((M : ℤ) + 1 + k)) =
        ∑' k : ℕ, sigM ((M : ℤ) + 1 + k) * sample ((2 * M + 3 : ℤ) + 2 * k) ^ 2 := by
      apply tsum_congr
      intro k
      rw [hfM]
      dsimp only
      rw [show (2 * ((M : ℤ) + 1 + k) + 1) = (2 * M + 3 : ℤ) + 2 * k by push_cast; ring]
    rw [he]
    apply tsum_tail_le_pos (2 * M + 3 : ℤ) (by omega)
    · intro k
      exact sigM_nonneg _
    · intro k
      calc sigM ((M : ℤ) + 1 + k) ≤ |6 * (((M : ℤ) + 1 + k : ℤ) : ℝ) + 4| :=
            sigM_le_abs _
        _ = 6 * (k : ℝ) + (6 * M + 10) := by
            rw [abs_of_nonneg (by push_cast; positivity)]
            push_cast
            ring
  -- M⁻ tail.
  have hMneg : (∑' k : ℕ, fM (-((M : ℤ) + 1) - k)) ≤
      tailLeading (fun i => ((2 * M + 1 - shift i : ℤ) : ℝ))
        + tailError (fun i => ((2 * M + 1 - shift i : ℤ) : ℝ)) (6 * M + 2) := by
    have he : (∑' k : ℕ, fM (-((M : ℤ) + 1) - k)) =
        ∑' k : ℕ, sigM (-((M : ℤ) + 1) - k) * sample (-(2 * M + 1 : ℤ) - 2 * k) ^ 2 := by
      apply tsum_congr
      intro k
      rw [hfM]
      dsimp only
      rw [show (2 * (-((M : ℤ) + 1) - k) + 1) = -(2 * M + 1 : ℤ) - 2 * k by push_cast; ring]
    rw [he]
    apply tsum_tail_le_neg (2 * M + 1 : ℤ) (by omega)
    · intro k
      exact sigM_nonneg _
    · intro k
      calc sigM (-((M : ℤ) + 1) - k) ≤ |6 * ((-((M : ℤ) + 1) - k : ℤ) : ℝ) + 4| :=
            sigM_le_abs _
        _ = 6 * (k : ℝ) + (6 * M + 2) := by
            rw [show (6 * ((-((M : ℤ) + 1) - k : ℤ) : ℝ) + 4) =
              -(6 * (k : ℝ) + (6 * M + 2)) by push_cast; ring, abs_neg,
              abs_of_nonneg (by positivity)]
  -- Assemble.
  have hPle : (∑' n : ℤ, sigP n * ‖trial n‖ ^ 2) ≤
      (∑ n ∈ Finset.Icc (-(M : ℤ)) M, sigP n * sample (2 * n) ^ 2)
        + ((tailLeading (fun i => ((2 * M + 2 + shift i : ℤ) : ℝ))
            + tailError (fun i => ((2 * M + 2 + shift i : ℤ) : ℝ)) (6 * M + 7))
          + (tailLeading (fun i => ((2 * M + 2 - shift i : ℤ) : ℝ))
            + tailError (fun i => ((2 * M + 2 - shift i : ℤ) : ℝ)) (6 * M + 5))) := by
    rw [hPeq, hPsplit]
    have : (∑ n ∈ Finset.Icc (-(M : ℤ)) M, fP n) =
        ∑ n ∈ Finset.Icc (-(M : ℤ)) M, sigP n * sample (2 * n) ^ 2 := rfl
    linarith [hPpos, hPneg]
  have hMle : (∑' m : ℤ, sigM m * ‖convS trial m‖ ^ 2) ≤
      (∑ m ∈ Finset.Icc (-(M : ℤ)) M, sigM m * sample (2 * m + 1) ^ 2)
        + ((tailLeading (fun i => ((2 * M + 3 + shift i : ℤ) : ℝ))
            + tailError (fun i => ((2 * M + 3 + shift i : ℤ) : ℝ)) (6 * M + 10))
          + (tailLeading (fun i => ((2 * M + 1 - shift i : ℤ) : ℝ))
            + tailError (fun i => ((2 * M + 1 - shift i : ℤ) : ℝ)) (6 * M + 2))) := by
    rw [hMeq, hMsplit]
    linarith [hMpos, hMneg]
  have hs2 := mul_le_mul_of_nonneg_left hMle (sq_nonneg s)
  rw [CircleQ.Qform]
  linarith

end KsIndex.AlphaRemarkTrial
