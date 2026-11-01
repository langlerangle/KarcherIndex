module

public import Mathlib

@[expose] public section


/-! A tail allowance for the four-mode Fourier Gram certificate.
The estimate holds for every weight offset t >= 5, so it can be used
at different spectral parameters. -/
noncomputable section
open scoped BigOperators
namespace KsIndex.AlphaTailTask

-- The four modes are -2, -1, 0 and 1.
def mode (i : Fin 4) : ℤ := (i.val : ℤ) - 2

def weight (t : ℝ) (n : ℤ) : ℝ :=
  (((6 * (n : ℝ) + 1)^2 - 4) / |6 * (n : ℝ) + 1|) + t

def kernel (i : Fin 4) (n : ℤ) : ℝ :=
  (-1 : ℝ) ^ (mode i - n) / (2 * ((mode i : ℝ) - (n : ℝ)) + 1)

def mixedKernel (a : Fin 4 → ℂ) (n : ℤ) : ℂ :=
  ∑ i, (kernel i n : ℂ) * a i

def energy (t : ℝ) (a : Fin 4 → ℂ) (n : ℤ) : ℝ :=
  ‖mixedKernel a n‖ ^ 2 / weight t n

/-- The factor accounts for both tails beyond [-N,N]. -/
def tailAllowance (N : ℕ) : ℝ :=
  2 / (3 * (N : ℝ)^2 * (2 - 3 / ((N : ℝ) + 1))^2)

lemma weight_ge (t : ℝ) (ht : 5 ≤ t) (n : ℤ) : 6 * |(n : ℝ)| ≤ weight t n := by
  unfold weight
  rcases le_or_gt 0 n with h | h
  · have h0 : (0:ℝ) ≤ n := by exact_mod_cast h
    have hx : (1:ℝ) ≤ 6 * (n : ℝ) + 1 := by linarith
    rw [abs_of_nonneg h0, abs_of_pos (by linarith)]
    rw [div_add' _ _ _ (by linarith), le_div_iff₀ (by linarith)]
    nlinarith
  · have h0 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
    rw [div_add' _ _ _ (by linarith), le_div_iff₀ (by linarith)]
    nlinarith

lemma kernel_bound (i : Fin 4) (n : ℤ) (d : ℝ) (hd : d * |(n : ℝ)| ≤ 2 * |(n : ℝ)| - 3)
    (hpos : 0 < d * |(n : ℝ)|) : |kernel i n| ≤ 1 / (d * |(n : ℝ)|) := by
  unfold kernel
  rw [abs_div, abs_zpow, abs_neg, abs_one, one_zpow]
  apply one_div_le_one_div_of_le hpos
  have hm : |2 * (mode i : ℝ) + 1| ≤ 3 := by
    fin_cases i <;> norm_num [mode]
  have := abs_sub_abs_le_abs_sub (2 * (n : ℝ)) (2 * (mode i : ℝ) + 1)
  rw [abs_mul, abs_two] at this
  calc d * |(n : ℝ)| ≤ 2 * |(n : ℝ)| - 3 := hd
    _ ≤ |2 * (n : ℝ) - (2 * (mode i : ℝ) + 1)| := by linarith
    _ = |2 * ((mode i : ℝ) - (n : ℝ)) + 1| := by
        rw [← abs_neg]; ring_nf

lemma mixed_sq_le (a : Fin 4 → ℂ) (n : ℤ) (B : ℝ) (hB : ∀ i, |kernel i n| ≤ B) :
    ‖mixedKernel a n‖ ^ 2 ≤ 4 * B ^ 2 * ∑ i, ‖a i‖ ^ 2 := by
  have h1 : ‖mixedKernel a n‖ ≤ ∑ i, |kernel i n| * ‖a i‖ := by
    unfold mixedKernel
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |kernel i n|) (fun i => ‖a i‖)
  have h3 : ∑ i, |kernel i n| ^ 2 ≤ ∑ _i : Fin 4, B ^ 2 :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hB i) 2
  have h4 : ∑ _i : Fin 4, B ^ 2 = 4 * B ^ 2 := by simp
  have hS : 0 ≤ ∑ i, ‖a i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  calc ‖mixedKernel a n‖ ^ 2 ≤ (∑ i, |kernel i n| * ‖a i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i, |kernel i n| ^ 2) * ∑ i, ‖a i‖ ^ 2 := h2
    _ ≤ 4 * B ^ 2 * ∑ i, ‖a i‖ ^ 2 := by
        rw [← h4]; exact mul_le_mul_of_nonneg_right h3 hS

/-- Pointwise tail estimate. -/
lemma energy_tail_le (t : ℝ) (ht : 5 ≤ t) (N : ℕ) (hN : 1 ≤ N) (a : Fin 4 → ℂ) (n : ℤ)
    (hn : (N : ℝ) + 1 ≤ |(n : ℝ)|) :
    0 ≤ energy t a n ∧
    energy t a n ≤ 2 / (3 * (2 - 3 / ((N : ℝ) + 1)) ^ 2) * (∑ i, ‖a i‖ ^ 2) / |(n : ℝ)| ^ 3 := by
  set d : ℝ := 2 - 3 / ((N : ℝ) + 1) with hd_def
  set m : ℝ := |(n : ℝ)| with hm_def
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (0:ℝ) < (N:ℝ) + 1 := by linarith
  have hd : 1 / 2 ≤ d := by
    rw [hd_def]
    have : 3 / ((N:ℝ) + 1) ≤ 3 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by
      linarith)
    linarith
  have hm0 : 0 < m := by linarith
  have hdm : d * m ≤ 2 * m - 3 := by
    rw [hd_def]
    have : 3 ≤ 3 / ((N:ℝ) + 1) * m := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hN1]; nlinarith
    nlinarith
  have hpos : 0 < d * m := by positivity
  have hw : 6 * m ≤ weight t n := weight_ge t ht n
  have hwpos : 0 < weight t n := by linarith
  have hS : 0 ≤ ∑ i, ‖a i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hM := mixed_sq_le a n (1 / (d * m)) fun i => kernel_bound i n d hdm hpos
  refine ⟨div_nonneg (by positivity) hwpos.le, ?_⟩
  unfold energy
  rw [div_le_iff₀ hwpos]
  calc ‖mixedKernel a n‖ ^ 2 ≤ 4 * (1 / (d * m)) ^ 2 * ∑ i, ‖a i‖ ^ 2 := hM
    _ = 2 / (3 * d ^ 2) * (∑ i, ‖a i‖ ^ 2) / m ^ 3 * (6 * m) := by
        field_simp; ring
    _ ≤ 2 / (3 * d ^ 2) * (∑ i, ‖a i‖ ^ 2) / m ^ 3 * weight t n := by
        apply mul_le_mul_of_nonneg_left hw; positivity

/-- Telescoping tail lemma. -/
lemma tsum_le_of_telescope (f u : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hu : ∀ k, 0 ≤ u k)
    (hf0 : ∀ k, 0 ≤ f k) (hf : ∀ k, f k ≤ B * (u k - u (k + 1))) :
    Summable f ∧ ∑' k, f k ≤ B * u 0 := by
  have hpart : ∀ K, ∑ k ∈ Finset.range K, f k ≤ B * u 0 := by
    intro K
    calc ∑ k ∈ Finset.range K, f k ≤ ∑ k ∈ Finset.range K, B * (u k - u (k + 1)) :=
          Finset.sum_le_sum fun k _ => hf k
      _ = B * (u 0 - u K) := by rw [← Finset.mul_sum, Finset.sum_range_sub']
      _ ≤ B * u 0 := by nlinarith [hu K]
  exact ⟨summable_of_sum_range_le hf0 hpart, Real.tsum_le_of_sum_range_le hf0 hpart⟩

lemma cube_telescope (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    1 / ((k : ℝ) + N + 1) ^ 3 ≤
      (1 / 2) * (1 / (((k:ℝ) + N) * ((k:ℝ) + N + 1)) -
        1 / ((((k + 1 : ℕ) : ℝ) + N) * (((k + 1 : ℕ) : ℝ) + N + 1))) := by
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hk : (0:ℝ) ≤ k := by positivity
  push_cast
  have hx : (1:ℝ) ≤ (k:ℝ) + N := by linarith
  have e : (1 / 2 : ℝ) * (1 / (((k:ℝ) + N) * ((k:ℝ) + N + 1)) -
        1 / (((k:ℝ) + 1 + N) * ((k:ℝ) + 1 + N + 1))) =
        1 / (((k:ℝ) + N) * ((k:ℝ) + N + 1) * ((k:ℝ) + N + 2)) := by
    field_simp; ring
  rw [e]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- Combined per-term tail bound for both signs. -/
lemma tail_term_le (t : ℝ) (ht : 5 ≤ t) (N : ℕ) (hN : 1 ≤ N) (a : Fin 4 → ℂ) (n : ℤ) (k : ℕ)
    (hn : |(n : ℝ)| = (k : ℝ) + N + 1) :
    0 ≤ energy t a n ∧
    energy t a n ≤ (2 / (3 * (2 - 3 / ((N : ℝ) + 1)) ^ 2) * (∑ i, ‖a i‖ ^ 2) / 2) *
      (1 / (((k:ℝ) + N) * ((k:ℝ) + N + 1)) -
        1 / ((((k + 1 : ℕ) : ℝ) + N) * (((k + 1 : ℕ) : ℝ) + N + 1))) := by
  have hk : (0:ℝ) ≤ k := by positivity
  obtain ⟨h0, h1⟩ := energy_tail_le t ht N hN a n (by rw [hn]; linarith)
  refine ⟨h0, h1.trans ?_⟩
  have hS : 0 ≤ ∑ i, ‖a i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hC : 0 ≤ 2 / (3 * (2 - 3 / ((N : ℝ) + 1)) ^ 2) * (∑ i, ‖a i‖ ^ 2) := by positivity
  have := mul_le_mul_of_nonneg_left (cube_telescope N hN k) hC
  rw [hn, div_eq_mul_one_div _ (((k:ℝ) + N + 1) ^ 3)]
  linarith

/-- Exact tail allowance at cutoff 64. -/
lemma tailAllowance_64 : tailAllowance 64 = 4225 / 99096576 := by
  unfold tailAllowance; norm_num

/-- Both tails outside `[-N,N]` are summable and satisfy the combined bound
for every complex four-vector, weight offset `t ≥ 5`, and cutoff `N ≥ 2`. -/
theorem tails_summable_and_bound (t : ℝ) (ht : 5 ≤ t)
    (N : ℕ) (hN : 2 ≤ N) (a : Fin 4 → ℂ) :
    Summable (fun n : ℕ => energy t a ((n : ℤ) + (N : ℤ) + 1)) ∧
    Summable (fun n : ℕ => energy t a (-((n : ℤ) + (N : ℤ) + 1))) ∧
    (∑' n : ℕ, energy t a ((n : ℤ) + (N : ℤ) + 1)) +
      (∑' n : ℕ, energy t a (-((n : ℤ) + (N : ℤ) + 1))) ≤
      tailAllowance N * (∑ i, ‖a i‖^2) := by
  have hN1 : 1 ≤ N := by omega
  have hN' : (2:ℝ) ≤ N := by exact_mod_cast hN
  set u : ℕ → ℝ := fun k => 1 / (((k:ℝ) + N) * ((k:ℝ) + N + 1)) with hu_def
  set B : ℝ := 2 / (3 * (2 - 3 / ((N : ℝ) + 1)) ^ 2) * (∑ i, ‖a i‖ ^ 2) / 2 with hB_def
  have hS : 0 ≤ ∑ i, ‖a i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hB : 0 ≤ B := by positivity
  have hu : ∀ k, 0 ≤ u k := fun k => by positivity
  have hpos : ∀ k : ℕ, |(((k : ℤ) + (N : ℤ) + 1 : ℤ) : ℝ)| = (k : ℝ) + N + 1 := by
    intro k; push_cast; exact abs_of_nonneg (by positivity)
  have hneg : ∀ k : ℕ, |((-((k : ℤ) + (N : ℤ) + 1) : ℤ) : ℝ)| = (k : ℝ) + N + 1 := by
    intro k; push_cast; rw [abs_neg]; exact abs_of_nonneg (by positivity)
  obtain ⟨s1, b1⟩ := tsum_le_of_telescope _ u B hB hu
    (fun k => (tail_term_le t ht N hN1 a _ k (hpos k)).1)
    (fun k => (tail_term_le t ht N hN1 a _ k (hpos k)).2)
  obtain ⟨s2, b2⟩ := tsum_le_of_telescope _ u B hB hu
    (fun k => (tail_term_le t ht N hN1 a _ k (hneg k)).1)
    (fun k => (tail_term_le t ht N hN1 a _ k (hneg k)).2)
  refine ⟨s1, s2, ?_⟩
  have key : 2 * B * u 0 ≤ tailAllowance N * (∑ i, ‖a i‖^2) := by
    rw [hB_def, hu_def, tailAllowance]
    have hd : 0 < 2 - 3 / ((N : ℝ) + 1) := by
      have : 3 / ((N:ℝ) + 1) ≤ 3 / 3 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      linarith
    simp only [Nat.cast_zero, zero_add]
    have e1 : 2 * (2 / (3 * (2 - 3 / ((N : ℝ) + 1)) ^ 2) * (∑ i, ‖a i‖ ^ 2) / 2) *
        (1 / ((N:ℝ) * ((N:ℝ) + 1))) =
        (2 / (3 * (2 - 3 / ((N : ℝ) + 1)) ^ 2) * (∑ i, ‖a i‖ ^ 2)) * (1 / ((N:ℝ) * ((N:ℝ) + 1)))
          := by
      ring
    have e2 : 2 / (3 * (N : ℝ)^2 * (2 - 3 / ((N : ℝ) + 1))^2) * (∑ i, ‖a i‖ ^ 2) =
        (2 / (3 * (2 - 3 / ((N : ℝ) + 1)) ^ 2) * (∑ i, ‖a i‖ ^ 2)) * (1 / (N:ℝ) ^ 2) := by
      field_simp
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  linarith

/-- Assembly into the full integer Gram sum; the finite window has 2N+1 terms. -/
theorem full_sum_bound (t : ℝ) (ht : 5 ≤ t)
    (N : ℕ) (hN : 2 ≤ N) (a : Fin 4 → ℂ) :
    Summable (energy t a) ∧
    (∑' n : ℤ, energy t a n) ≤
      (∑ n ∈ Finset.range (2 * N + 1), energy t a ((n : ℤ) - (N : ℤ))) +
      tailAllowance N * (∑ i, ‖a i‖^2) := by
  obtain ⟨s1, s2, hb⟩ := tails_summable_and_bound t ht N hN a
  set g : ℤ → ℝ := fun n => energy t a (n - N) with hg
  have hg1 : (fun n : ℕ => g ((n + (2 * N + 1) : ℕ) : ℤ)) =
      fun n : ℕ => energy t a ((n : ℤ) + (N : ℤ) + 1) := by
    funext n; simp only [hg]; congr 1; push_cast; ring
  have hg2 : (fun n : ℕ => g (-((n : ℤ) + 1))) =
      fun n : ℕ => energy t a (-((n : ℤ) + (N : ℤ) + 1)) := by
    funext n; simp only [hg]; congr 1; ring
  have sg1 : Summable (fun n : ℕ => g n) := by
    rw [← summable_nat_add_iff (2 * N + 1)]
    have : (fun n : ℕ => g ((n + (2 * N + 1) : ℕ) : ℤ)) =
        fun n : ℕ => (fun m : ℕ => g m) (n + (2 * N + 1)) := rfl
    rw [← this, hg1]; exact s1
  have sg2 : Summable (fun n : ℕ => g (-((n : ℤ) + 1))) := by rw [hg2]; exact s2
  have sg : Summable g := Summable.of_nat_of_neg_add_one sg1 sg2
  have e : ∀ n : ℤ, energy t a n = g (n + N) := fun n => by simp [hg]
  have hfg : (∑' n : ℤ, energy t a n) = ∑' n : ℤ, g n := by
    rw [show (∑' n : ℤ, energy t a n) = ∑' n : ℤ, g (Equiv.addRight (N : ℤ) n) from
      tsum_congr fun n => e n]
    exact Equiv.tsum_eq (Equiv.addRight (N : ℤ)) g
  have sf : Summable (energy t a) := by
    have : energy t a = g ∘ (Equiv.addRight (N : ℤ)) := funext e
    rw [this]; exact (Equiv.summable_iff _).mpr sg
  refine ⟨sf, ?_⟩
  rw [hfg, tsum_of_nat_of_neg_add_one sg1 sg2, ← sg1.sum_add_tsum_nat_add (2 * N + 1)]
  have h1 : (∑' n : ℕ, g ((n + (2 * N + 1) : ℕ) : ℤ)) =
      ∑' n : ℕ, energy t a ((n : ℤ) + (N : ℤ) + 1) := by rw [hg1]
  have h2 : (∑' n : ℕ, g (-((n : ℤ) + 1))) =
      ∑' n : ℕ, energy t a (-((n : ℤ) + (N : ℤ) + 1)) := by rw [hg2]
  rw [h1, h2]
  linarith

/-- At weight offset `363/16`, the terms outside `[-64,64]` contribute
at most `1/23000` times the squared coefficient norm. -/
theorem production_tail_bound (a : Fin 4 → ℂ) :
    (∑' n : ℤ, energy (363/16) a n) ≤
      (∑ n ∈ Finset.range 129, energy (363/16) a ((n : ℤ) - 64)) +
      (1/23000 : ℝ) * (∑ i, ‖a i‖^2) := by
  have h := (full_sum_bound (363/16) (by norm_num) 64 (by norm_num) a).2
  have hT : tailAllowance 64 ≤ 1 / 23000 := by
    unfold tailAllowance; norm_num
  have hS : 0 ≤ ∑ i, ‖a i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have := mul_le_mul_of_nonneg_right hT hS
  simp only [show 2 * 64 + 1 = 129 from rfl, Nat.cast_ofNat] at h
  linarith

end KsIndex.AlphaTailTask
