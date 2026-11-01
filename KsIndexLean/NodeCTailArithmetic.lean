module

public import Mathlib

@[expose] public section


/-!
# Tail arithmetic for the single-arc trial field

The arithmetic lemmas were produced by Aristotle, project
`9b589f18-c554-4ca6-8662-f13cee0b5236`, run
`24ee8b81-d47f-4109-8216-23d3d413394a`. Astra prepared the problem and checked
the return on the project pins. Port changes consisted of the header and
updates to deprecated `ite` lemma names. `NodeCTail` supplies the concrete
Fourier coefficient data for these abstract estimates.
-/
noncomputable section
namespace AristotleTail

def sigma (k : ℕ) (a : ℝ) (n : ℤ) : ℝ :=
  (((n : ℝ) + a) ^ 2 - (1 - 1 / (k : ℝ)) ^ 2) / |(n : ℝ) + a|

def Hs (s : ℝ) : ℝ := 3 * (s + 1) / (s * (s + 6))

/-- Abstract squared Fourier coefficients, supplied by four proved project lemmas. -/
def CoeffData (b : ℤ → ℝ) : Prop :=
  b 0 = 0 ∧ b (-1) = 0 ∧
  (∀ t : ℤ, t ≠ 0 →
    b (2 * t) = 4 / ((2 + Real.pi) ^ 2 * (((2 * t + 1 : ℤ) : ℝ) ^ 2))) ∧
  (∀ t : ℤ, t ≠ -1 →
    b (2 * t + 1) = 4 / ((2 + Real.pi) ^ 2 * (((2 * t + 1 : ℤ) : ℝ) ^ 2)))

/-- The `k → ∞` limit of `sigma k a n`. -/
def sigmaInf (a : ℝ) (n : ℤ) : ℝ :=
  (((n : ℝ) + a) ^ 2 - 1) / |(n : ℝ) + a|

lemma one_lt_abs_add {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {n : ℤ}
    (h0 : n ≠ 0) (h1 : n ≠ -1) : 1 < |(n : ℝ) + a| := by
  rcases (show 1 ≤ n ∨ n ≤ -2 by omega) with h | h
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]; linarith
  · have : (n : ℝ) ≤ -2 := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]; linarith

lemma sigmaInf_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {n : ℤ}
    (h0 : n ≠ 0) (h1 : n ≠ -1) : 0 < sigmaInf a n := by
  have hx := one_lt_abs_add ha0 ha1 h0 h1
  unfold sigmaInf
  rw [← sq_abs]
  apply div_pos _ (by linarith)
  nlinarith

lemma sigmaInf_lt_sigma {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {n : ℤ}
    (h0 : n ≠ 0) (h1 : n ≠ -1) : sigmaInf a n < sigma k a n := by
  have hx := one_lt_abs_add ha0 ha1 h0 h1
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc0 : 0 ≤ 1 - 1 / (k : ℝ) := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact hk'
  have hc1 : 1 - 1 / (k : ℝ) < 1 := by
    have : 0 < 1 / (k : ℝ) := by positivity
    linarith
  unfold sigmaInf sigma
  apply div_lt_div_of_pos_right _ (by linarith)
  nlinarith

lemma coeff_formula {b : ℤ → ℝ} (hb : CoeffData b) {m : ℤ} (h0 : m ≠ 0) (h1 : m ≠ -1) :
    ∃ r : ℤ, r ≠ 0 ∧ |(m : ℝ)| - 1 ≤ |(r : ℝ)| ∧
      b m = 4 / ((2 + Real.pi) ^ 2 * ((r : ℝ) ^ 2)) := by
  obtain ⟨t, rfl | rfl⟩ := Int.even_or_odd' m
  · refine ⟨2 * t + 1, by omega, ?_, hb.2.2.1 t (by omega)⟩
    have h := abs_sub_abs_le_abs_sub ((2 : ℝ) * t) (-1)
    rw [abs_neg, abs_one, sub_neg_eq_add] at h
    push_cast
    exact h
  · refine ⟨2 * t + 1, by omega, by linarith, hb.2.2.2 t (by omega)⟩

lemma coeff_nonneg {b : ℤ → ℝ} (hb : CoeffData b) (m : ℤ) : 0 ≤ b m := by
  by_cases h0 : m = 0
  · rw [h0, hb.1]
  by_cases h1 : m = -1
  · rw [h1, hb.2.1]
  obtain ⟨r, -, -, hr⟩ := coeff_formula hb h0 h1
  rw [hr]; positivity

lemma term_nonneg {b : ℤ → ℝ} (hb : CoeffData b) {k : ℕ} (hk : 1 ≤ k) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (n : ℤ) : 0 ≤ b n / sigma k a n := by
  by_cases h0 : n = 0
  · rw [h0, hb.1, zero_div]
  by_cases h1 : n = -1
  · rw [h1, hb.2.1, zero_div]
  exact div_nonneg (coeff_nonneg hb n)
    ((sigmaInf_pos ha0 ha1 h0 h1).trans (sigmaInf_lt_sigma hk ha0 ha1 h0 h1)).le

lemma term_le_inf {b : ℤ → ℝ} (hb : CoeffData b) {k : ℕ} (hk : 1 ≤ k) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) {n : ℤ} (h0 : n ≠ 0) (h1 : n ≠ -1) :
    b n / sigma k a n ≤ b n / sigmaInf a n :=
  div_le_div_of_nonneg_left (coeff_nonneg hb n) (sigmaInf_pos ha0 ha1 h0 h1)
    (sigmaInf_lt_sigma hk ha0 ha1 h0 h1).le

/-- Far-tail estimate: `b n / sigma ≤ 16 / (3 (2+π)^2) / (|n| - 1)^3`. -/
lemma term_le_far {b : ℤ → ℝ} (hb : CoeffData b) {k : ℕ} (hk : 1 ≤ k) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) {n : ℤ} (h0 : n ≠ 0) (h1 : n ≠ -1) {y : ℝ}
    (hy : y = |(n : ℝ)| - 1) (hy1 : 1 ≤ y) (hyx : y ≤ |(n : ℝ) + a|)
    (hx2 : 2 ≤ |(n : ℝ) + a|) :
    b n / sigma k a n ≤ 16 / (3 * (2 + Real.pi) ^ 2) / y ^ 3 := by
  refine (term_le_inf hb hk ha0 ha1 h0 h1).trans ?_
  obtain ⟨r, -, hr, hbr⟩ := coeff_formula hb h0 h1
  set x := |(n : ℝ) + a| with hxdef
  set P := (2 + Real.pi) ^ 2 with hP
  have hPpos : 0 < P := by positivity
  have hsI : sigmaInf a n = (x ^ 2 - 1) / x := by
    simp only [sigmaInf, hxdef, sq_abs]
  have hsI' : 3 * y / 4 ≤ sigmaInf a n := by
    rw [hsI, le_div_iff₀ (by linarith)]
    nlinarith
  have hr2 : y ^ 2 ≤ (r : ℝ) ^ 2 := by
    rw [← sq_abs (r : ℝ)]
    exact pow_le_pow_left₀ (by linarith) (by rw [hy]; exact hr) 2
  have hbn : b n ≤ 4 / (P * y ^ 2) := by
    rw [hbr]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_left hr2 hPpos.le
  calc b n / sigmaInf a n ≤ (4 / (P * y ^ 2)) / (3 * y / 4) := by
        apply div_le_div₀ (by positivity) hbn (by positivity) hsI'
    _ = 16 / (3 * P) / y ^ 3 := by
        field_simp; ring

lemma pair_identity {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    1 / sigmaInf a 1 + 1 / sigmaInf a (-2) = Hs (a * (1 - a)) := by
  unfold sigmaInf Hs
  push_cast
  rw [abs_of_pos (by linarith : (0 : ℝ) < 1 + a),
    abs_of_neg (by linarith : (-2 : ℝ) + a < 0)]
  have h1 : (1 + a) ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : (-2 + a) ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : a * (1 - a) ≠ 0 := by nlinarith
  have h4 : a * (1 - a) + 6 ≠ 0 := by nlinarith
  have h5 : (1 + a) ≠ 0 := by linarith
  have h6 : -(-2 + a) ≠ 0 := by linarith
  have h7 : 1 - a ≠ 0 := by linarith
  have h8 : a ≠ 0 := by linarith
  field_simp
  ring

/-- Positive-side far weights `1/(n-1)^3` for `n ≥ 2`. -/
def pw (n : ℕ) : ℝ := if 2 ≤ n then 1 / ((n : ℝ) - 1) ^ 3 else 0

/-- Negative-side far weights `1/n^3` for `n ≥ 2`. -/
def qw (n : ℕ) : ℝ := if 2 ≤ n then 1 / (n : ℝ) ^ 3 else 0

lemma pw_nonneg (n : ℕ) : 0 ≤ pw n := by
  unfold pw; split_ifs with h
  · have : (2 : ℝ) ≤ n := by exact_mod_cast h
    have : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    positivity
  · rfl

lemma qw_nonneg (n : ℕ) : 0 ≤ qw n := by
  unfold qw; split_ifs <;> positivity

/-- Integral-comparison step: `1/m^3 ≤ (1/(m-1)^2 - 1/m^2)/2`, i.e.
`1/m^3 ≤ ∫_{m-1}^m x^{-3} dx`. -/
lemma cube_le_telescope {m : ℝ} (hm : 2 ≤ m) :
    1 / m ^ 3 ≤ (1 / (m - 1) ^ 2 - 1 / m ^ 2) / 2 := by
  have h1 : 0 < m - 1 := by linarith
  have h2 : 0 < m := by linarith
  rw [div_sub_div _ _ (by positivity) (by positivity), div_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos h1 h2, mul_pos (mul_pos h1 h2) h2, mul_pos (mul_pos h1 h2) h1]

lemma qw_sum_aux (N : ℕ) :
    ∑ i ∈ Finset.range (N + 2), qw i ≤ 1 / 2 - 1 / (2 * ((N : ℝ) + 1) ^ 2) := by
  induction N with
  | zero => simp [Finset.sum_range_succ, qw]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hq : qw (N + 2) = 1 / ((N : ℝ) + 2) ^ 3 := by
      simp [qw]
    have := cube_le_telescope (m := (N : ℝ) + 2) (by linarith [N.cast_nonneg (α := ℝ)])
    rw [hq]
    push_cast
    have e1 : (N : ℝ) + 2 - 1 = N + 1 := by ring
    rw [e1] at this
    have e2 : ((N : ℝ) + 1 + 1) = N + 2 := by ring
    rw [e2]
    have e3 : 1 / (2 * ((N : ℝ) + 1) ^ 2) = 1 / ((N : ℝ) + 1) ^ 2 / 2 := by rw [div_div, mul_comm]
    have e4 : 1 / (2 * ((N : ℝ) + 2) ^ 2) = 1 / ((N : ℝ) + 2) ^ 2 / 2 := by rw [div_div, mul_comm]
    rw [e3] at ih; rw [e4]
    linarith

lemma pw_sum_aux (N : ℕ) :
    ∑ i ∈ Finset.range (N + 3), pw i ≤ 3 / 2 - 1 / (2 * ((N : ℝ) + 1) ^ 2) := by
  induction N with
  | zero => norm_num [Finset.sum_range_succ, pw]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hp : pw (N + 3) = 1 / ((N : ℝ) + 2) ^ 3 := by
      simp [pw]; ring_nf
    have := cube_le_telescope (m := (N : ℝ) + 2) (by linarith [N.cast_nonneg (α := ℝ)])
    rw [hp]
    push_cast
    have e1 : (N : ℝ) + 2 - 1 = N + 1 := by ring
    rw [e1] at this
    have e2 : ((N : ℝ) + 1 + 1) = N + 2 := by ring
    rw [e2]
    have e3 : 1 / (2 * ((N : ℝ) + 1) ^ 2) = 1 / ((N : ℝ) + 1) ^ 2 / 2 := by rw [div_div, mul_comm]
    have e4 : 1 / (2 * ((N : ℝ) + 2) ^ 2) = 1 / ((N : ℝ) + 2) ^ 2 / 2 := by rw [div_div, mul_comm]
    rw [e3] at ih; rw [e4]
    linarith

lemma sum_range_le_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (N j : ℕ) :
    ∑ i ∈ Finset.range N, f i ≤ ∑ i ∈ Finset.range (N + j), f i :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
    (fun i _ _ => hf i)

lemma qw_sum_le (N : ℕ) : ∑ i ∈ Finset.range N, qw i ≤ 1 / 2 := by
  refine (sum_range_le_of_nonneg qw_nonneg N 2).trans ((qw_sum_aux N).trans ?_)
  have : 0 ≤ 1 / (2 * ((N : ℝ) + 1) ^ 2) := by positivity
  linarith

lemma pw_sum_le (N : ℕ) : ∑ i ∈ Finset.range N, pw i ≤ 3 / 2 := by
  refine (sum_range_le_of_nonneg pw_nonneg N 3).trans ((pw_sum_aux N).trans ?_)
  have : 0 ≤ 1 / (2 * ((N : ℝ) + 1) ^ 2) := by positivity
  linarith

lemma pos_bound {b : ℤ → ℝ} (hb : CoeffData b) {k : ℕ} (hk : 1 ≤ k) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    b n / sigma k a n ≤ (if n = 1 then b 1 / sigmaInf a 1 else 0) +
      16 / (3 * (2 + Real.pi) ^ 2) * pw n := by
  rcases n with _ | _ | n
  · simp [hb.1, pw]
  · simpa [pw] using term_le_inf hb hk ha0 ha1 (n := 1) (by norm_num) (by norm_num)
  · have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have hpw : pw (n + 2) = 1 / ((n : ℝ) + 1) ^ 3 := by
      simp only [pw, ite_eq_left (show 2 ≤ n + 2 by omega)]; push_cast; ring_nf
    rw [ite_eq_right (by omega), zero_add, hpw, mul_one_div]
    have habs : |(((n + 2 : ℕ) : ℤ) : ℝ)| = n + 2 := by
      push_cast; exact abs_of_pos (by linarith)
    have habs2 : |(((n + 2 : ℕ) : ℤ) : ℝ) + a| = n + 2 + a := by
      push_cast; exact abs_of_pos (by linarith)
    exact term_le_far hb hk ha0 ha1 (by omega) (by omega) (y := (n : ℝ) + 1)
      (by rw [habs]; ring) (by linarith) (by rw [habs2]; linarith) (by rw [habs2]; linarith)

lemma neg_bound {b : ℤ → ℝ} (hb : CoeffData b) {k : ℕ} (hk : 1 ≤ k) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    b (-(n + 1)) / sigma k a (-(n + 1)) ≤
      (if n = 1 then b (-2) / sigmaInf a (-2) else 0) +
      16 / (3 * (2 + Real.pi) ^ 2) * qw n := by
  rcases n with _ | _ | n
  · simp [hb.2.1, qw]
  · have := term_le_inf hb hk ha0 ha1 (n := -2) (by norm_num) (by norm_num)
    simp only [qw]
    norm_num
    exact this
  · have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have hqw : qw (n + 2) = 1 / ((n : ℝ) + 2) ^ 3 := by
      simp only [qw, ite_eq_left (show 2 ≤ n + 2 by omega)]; push_cast; ring_nf
    rw [ite_eq_right (by omega), zero_add, hqw, mul_one_div]
    have habs : |((-(((n + 2 : ℕ) : ℤ) + 1) : ℤ) : ℝ)| = n + 3 := by
      push_cast; rw [abs_of_neg (by linarith)]; ring
    have habs2 : |((-(((n + 2 : ℕ) : ℤ) + 1) : ℤ) : ℝ) + a| = n + 3 - a := by
      push_cast; rw [abs_of_neg (by linarith)]; ring
    exact term_le_far hb hk ha0 ha1 (by omega) (by omega) (y := (n : ℝ) + 2)
      (by rw [habs]; ring) (by linarith) (by rw [habs2]; linarith) (by rw [habs2]; linarith)

/-- Main estimate: summability together with the sharper bound
`4 Hs/(2+π)^2 + 32/(3(2+π)^2)`. -/
lemma tail_main (b : ℤ → ℝ) (hb : CoeffData b)
    {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Summable (fun n : ℤ => b n / sigma k a n) ∧
    (∑' n : ℤ, b n / sigma k a n) ≤
      4 * Hs (a * (1 - a)) / (2 + Real.pi) ^ 2 + 32 / (3 * (2 + Real.pi) ^ 2) := by
  set F : ℤ → ℝ := fun n => b n / sigma k a n with hF
  set C : ℝ := 16 / (3 * (2 + Real.pi) ^ 2) with hC
  have hC0 : 0 ≤ C := by positivity
  set A1 : ℝ := b 1 / sigmaInf a 1 with hA1
  set A2 : ℝ := b (-2) / sigmaInf a (-2) with hA2
  have hA1n : 0 ≤ A1 :=
    div_nonneg (coeff_nonneg hb 1) (sigmaInf_pos ha0 ha1 (by norm_num) (by norm_num)).le
  have hA2n : 0 ≤ A2 :=
    div_nonneg (coeff_nonneg hb (-2)) (sigmaInf_pos ha0 ha1 (by norm_num) (by norm_num)).le
  have hF0 : ∀ n, 0 ≤ F n := term_nonneg hb hk ha0 ha1
  -- partial sums on the nonnegative integers
  have hpos : ∀ N : ℕ, ∑ i ∈ Finset.range N, F i ≤ A1 + C * (3 / 2) := by
    intro N
    calc ∑ i ∈ Finset.range N, F i
        ≤ ∑ i ∈ Finset.range N, ((if i = 1 then A1 else 0) + C * pw i) :=
          Finset.sum_le_sum fun i _ => pos_bound hb hk ha0 ha1 i
      _ = (if 1 ∈ Finset.range N then A1 else 0) + C * ∑ i ∈ Finset.range N, pw i := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mul_sum]
      _ ≤ A1 + C * (3 / 2) := by
          gcongr
          · split_ifs <;> linarith
          · exact pw_sum_le N
  have hneg : ∀ N : ℕ, ∑ i ∈ Finset.range N, F (-(i + 1)) ≤ A2 + C * (1 / 2) := by
    intro N
    calc ∑ i ∈ Finset.range N, F (-(i + 1))
        ≤ ∑ i ∈ Finset.range N, ((if i = 1 then A2 else 0) + C * qw i) :=
          Finset.sum_le_sum fun i _ => neg_bound hb hk ha0 ha1 i
      _ = (if 1 ∈ Finset.range N then A2 else 0) + C * ∑ i ∈ Finset.range N, qw i := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mul_sum]
      _ ≤ A2 + C * (1 / 2) := by
          gcongr
          · split_ifs <;> linarith
          · exact qw_sum_le N
  have hs1 : Summable fun n : ℕ => F n := summable_of_sum_range_le (fun n => hF0 n) hpos
  have hs2 : Summable fun n : ℕ => F (-(n + 1)) :=
    summable_of_sum_range_le (fun n => hF0 _) hneg
  refine ⟨Summable.of_nat_of_neg_add_one hs1 hs2, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hs1 hs2]
  have t1 := Real.tsum_le_of_sum_range_le (fun n => hF0 n) hpos
  have t2 := Real.tsum_le_of_sum_range_le (fun n => hF0 _) hneg
  -- the two near modes `n = 1` and `n = -2`
  have hb1 : b 1 = 4 / (2 + Real.pi) ^ 2 := by
    have := hb.2.2.2 0 (by norm_num); norm_num at this; exact this
  have hb2 : b (-2) = 4 / (2 + Real.pi) ^ 2 := by
    have := hb.2.2.1 (-1) (by norm_num); norm_num at this; exact this
  have hpair : A1 + A2 = 4 * Hs (a * (1 - a)) / (2 + Real.pi) ^ 2 := by
    rw [hA1, hA2, hb1, hb2, ← pair_identity ha0 ha1]
    ring
  have hCC : C * (3 / 2) + C * (1 / 2) = 32 / (3 * (2 + Real.pi) ^ 2) := by
    rw [hC]; ring
  linarith

theorem tail_summable (b : ℤ → ℝ) (hb : CoeffData b)
    {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Summable (fun n : ℤ => b n / sigma k a n) := by
  exact (tail_main b hb hk ha0 ha1).1

theorem tail_bound (b : ℤ → ℝ) (hb : CoeffData b)
    {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (∑' n : ℤ, b n / sigma k a n) ≤
      4 * Hs (a * (1 - a)) / 25 + 32 / 75 := by
  refine (tail_main b hb hk ha0 ha1).2.trans ?_
  have hP : (25 : ℝ) ≤ (2 + Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  have hs : 0 < a * (1 - a) := mul_pos ha0 (by linarith)
  have hH : 0 < Hs (a * (1 - a)) := by unfold Hs; positivity
  have e1 : 4 * Hs (a * (1 - a)) / (2 + Real.pi) ^ 2 ≤ 4 * Hs (a * (1 - a)) / 25 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hP
  have e2 : 32 / (3 * (2 + Real.pi) ^ 2) ≤ 32 / 75 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  linarith

end AristotleTail
