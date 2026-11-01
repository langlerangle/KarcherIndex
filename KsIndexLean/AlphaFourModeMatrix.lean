module

public import KsIndexLean.AlphaFourModeGramTail

@[expose] public section


/-! Identification of the rational certificate and its complexification. -/
noncomputable section
namespace KsIndex.AlphaFourMode

def deficit : Fin 4 → ℝ := ![9/2, 12, 9, 12/5]

def roundedForm (x : Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, (roundedGram i j : ℝ) * x i * x j

lemma certificateForm_matrix (x : Fin 4 → ℝ) :
    certificateForm x = (∑ i, x i ^ 2 / ((121/64:ℝ) * deficit i)) -
      (10000/24649:ℝ) * (roundedForm x +
        (1/5120 + 4/10000000:ℝ) * ∑ i, x i ^ 2) := by
  norm_num [certificateForm, roundedForm, roundedGram, deficit, Fin.sum_univ_succ]
  ring

lemma certificateForm_nonneg (x : Fin 4 → ℝ) : 0 ≤ certificateForm x := by
  by_cases hx : x = 0
  · subst x; norm_num [certificateForm]
  · exact (certificateForm_pos hx).le

/-- The real certificate acts independently on real and imaginary parts. -/
def complexCertificate (a : Fin 4 → ℂ) : ℝ :=
  certificateForm (fun i => (a i).re) + certificateForm (fun i => (a i).im)

theorem complexCertificate_pos {a : Fin 4 → ℂ} (ha : a ≠ 0) :
    0 < complexCertificate a := by
  have h : (fun i => (a i).re) ≠ 0 ∨ (fun i => (a i).im) ≠ 0 := by
    by_contra! h
    apply ha
    funext i
    apply Complex.ext
    · exact congrFun h.1 i
    · exact congrFun h.2 i
  rcases h with h | h
  · exact add_pos_of_pos_of_nonneg (certificateForm_pos h) (certificateForm_nonneg _)
  · exact add_pos_of_nonneg_of_pos (certificateForm_nonneg _) (certificateForm_pos h)

lemma finiteGram_enclosure_real (i j : Fin 4) :
    |(finiteGram i j : ℝ) - (roundedGram i j : ℝ)| ≤ (1/10000000:ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).mpr (finiteGram_enclosure i j)
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

/-- Entrywise errors of size epsilon contribute at most four epsilon in dimension four. -/
lemma matrix_error_bound (E : Fin 4 → Fin 4 → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hE : ∀ i j, |E i j| ≤ ε) (x : Fin 4 → ℝ) :
    (∑ i, ∑ j, E i j * x i * x j) ≤ (4*ε) * ∑ i, x i ^ 2 := by
  have hp (i j : Fin 4) : E i j * x i * x j ≤ ε * |x i| * |x j| := by
    calc
      _ ≤ |E i j * x i * x j| := le_abs_self _
      _ = |E i j| * |x i| * |x j| := by rw [abs_mul, abs_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hE i j) (abs_nonneg _)) (abs_nonneg _)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
  have heq : (∑ i : Fin 4, ∑ j : Fin 4, ε * |x i| * |x j|) =
      ε * (∑ i : Fin 4, |x i|)^2 := by
    simp only [Fin.sum_univ_succ]
    ring
  have hc : (∑ i : Fin 4, |x i|)^2 ≤ 4 * ∑ i : Fin 4, x i ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin 4 => |x i|))
  rw [heq] at hs
  nlinarith [mul_le_mul_of_nonneg_left hc hε]

lemma finiteGram_form_le (x : Fin 4 → ℝ) :
    (∑ i, ∑ j, (finiteGram i j : ℝ) * x i * x j) ≤
      roundedForm x + (4/10000000:ℝ) * ∑ i, x i ^ 2 := by
  have h := matrix_error_bound (fun i j => (finiteGram i j : ℝ) - (roundedGram i j : ℝ))
    (1/10000000) (by positivity) finiteGram_enclosure_real x
  simp only [sub_mul, Finset.sum_sub_distrib] at h
  unfold roundedForm
  linarith

lemma rationalWeight_cast (n : ℤ) : (rationalWeight n : ℝ) = weight n := by
  unfold rationalWeight weight CircleQ.sigP
  push_cast
  ring

lemma rationalKernel_cast (i : Fin 4) (n : ℤ) :
    (rationalKernel (mode i) n : ℝ) = kernel i n := by
  unfold rationalKernel kernel
  push_cast
  ring

end KsIndex.AlphaFourMode
