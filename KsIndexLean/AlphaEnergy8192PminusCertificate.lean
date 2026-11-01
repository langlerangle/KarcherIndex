module

public import KsIndexLean.AlphaEnergy8192PminusErrors
public import KsIndexLean.ReciprocalWeightTail

@[expose] public section


/-! A numerical enclosure of the negative-frequency linear energy tail. -/
namespace KsIndex.AlphaRemarkTrial.Energy8192Tail.Pminus

/-- The actual infinite linear-weight tail, with all shifted trial coefficients. -/
theorem linear_tail_interval :
    |(∑' n : ℕ, (6*n+49157)*sample (-16386-2*n)^2) -
      (60479016934609/1000000000000000000 : ℝ)| ≤ (77/5000000000 : ℝ) := by
  have ht := trial_tail_interval point center radius 49157 point_ge radius_nonneg endpoint_interval
  have he : ∀ n : ℕ, sample (-16386-2*n) =
      ∑ i, tailScale i*PowerArc.g (exponent i) (point i+2*n) := by
    intro n
    simpa only [point, neg_one_mul, Int.cast_sub, Int.cast_add, Int.cast_neg, Int.cast_ofNat, sub_eq_add_neg] using sample_negative_tail 16386 n
  simp_rw [← he] at ht
  have h := (abs_sub_le (∑' n : ℕ, (6*n+49157)*sample (-16386-2*n)^2)
    (tailCenter point center) (60479016934609/1000000000000000000)).trans
    (add_le_add ht leading_interval)
  have hp := product_bound
  have hr := radius_bound
  linarith

theorem linear_tail_summable :
    Summable (fun n : ℕ => (6*n+49157)*sample (-16386-2*n)^2) := by
  let f := fun (i j : Fin 25) (n : ℕ) =>
    (6*n+49157)*(tailScale i*PowerArc.g (exponent i) (point i+2*n))*
      (tailScale j*PowerArc.g (exponent j) (point j+2*n))
  have hf (i j : Fin 25) : Summable (f i j) :=
    PowerArc.scaled_mixed_linear_summable (tailScale i) (tailScale j)
      (exponent_pos i) (exponent_pos j) (point_ge i) (point_ge j)
  have hs := summable_sum (fun i (_ : i ∈ Finset.univ) =>
    summable_sum (fun j (_ : j ∈ Finset.univ) => hf i j))
  apply hs.congr
  intro n
  have he : sample (-16386-2*n) =
      ∑ i, tailScale i*PowerArc.g (exponent i) (point i+2*n) := by
    simpa only [point, neg_one_mul, Int.cast_sub, Int.cast_add, Int.cast_neg, Int.cast_ofNat, sub_eq_add_neg] using sample_negative_tail 16386 n
  rw [he]
  simp only [f, pow_two, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- Full reciprocal-corrected symbol tail; no positive tail is discarded. -/
theorem corrected_tail_lower :
    (118093/1953125000 : ℝ) ≤
      ∑' n : ℕ, ((6*n+49157)-4/(6*n+49157))*sample (-16386-2*n)^2 := by
  have h := corrected_weight_tail_enclosure
    (fun n : ℕ => (6*(n:ℝ)+49157)) (fun n : ℕ => sample (-16386-2*n))
    49157 (60479016934609/1000000000000000000) (77/5000000000)
    (by norm_num) (fun n => by nlinarith [Nat.cast_nonneg (α := ℝ) n]) linear_tail_summable linear_tail_interval
  exact le_trans (by norm_num) h.2.1

end KsIndex.AlphaRemarkTrial.Energy8192Tail.Pminus
