module

public import KsIndexLean.PowerArcStieltjesRecurrence

@[expose] public section


/-! Rational moments of a summable sequence satisfying a linear recurrence.

These formulas retain the sign of the sequence and give exact endpoint values
for the first two terms of a Stieltjes tail expansion.
-/

namespace KsIndex.PowerArc

theorem recurrence_first_moment_hasSum {e : ℕ → ℝ} (he : Summable e)
    (A B : ℝ) (hB : 0 < B) (hgap : B - A ≠ 0)
    (hrec : ∀ k : ℕ, ((k : ℝ) + B) * e (k + 1) = ((k : ℝ) + A) * e k) :
    HasSum (fun k : ℕ => e k / ((k : ℝ) + B)) (e 0 / (B - A)) := by
  have ht : Summable (fun k => e (k + 1)) := (summable_nat_add_iff 1).2 he
  have htel : (∑' k, e k) - (∑' k, e (k + 1)) = e 0 := by
    have hh := he.tsum_eq_zero_add
    linarith
  have hid (k : ℕ) : e k / ((k : ℝ) + B) = (e k - e (k + 1)) / (B - A) := by
    have hk : 0 < (k : ℝ) + B := by positivity
    apply (div_eq_div_iff hk.ne' hgap).2
    nlinarith [hrec k]
  have hh := (he.hasSum.sub ht.hasSum).div_const (B - A)
  rw [htel] at hh
  simpa only [← hid] using hh

/-- Dividing by the recurrence denominator increases its parameter by one. -/
theorem divided_sequence_recurrence {e : ℕ → ℝ} (A B : ℝ) (hB : 0 < B)
    (hrec : ∀ k : ℕ, ((k : ℝ) + B) * e (k + 1) = ((k : ℝ) + A) * e k)
    (k : ℕ) :
    ((k : ℝ) + (B + 1)) * (e (k + 1) / ((k + 1 : ℕ) + B)) =
      ((k : ℝ) + A) * (e k / ((k : ℝ) + B)) := by
  have hk : 0 < (k : ℝ) + B := by positivity
  have hk1 : 0 < (k : ℝ) + 1 + B := by positivity
  push_cast
  rw [show (k : ℝ) + (B + 1) = k + 1 + B by ring, mul_div_cancel₀ _ hk1.ne']
  rw [← mul_div_assoc]
  apply (eq_div_iff hk.ne').2
  nlinarith [hrec k]

theorem recurrence_second_moment_hasSum {e : ℕ → ℝ} (he : Summable e)
    (A B : ℝ) (hB : 0 < B) (hgap : B + 1 - A ≠ 0)
    (hrec : ∀ k : ℕ, ((k : ℝ) + B) * e (k + 1) = ((k : ℝ) + A) * e k) :
    HasSum (fun k : ℕ => e k / (((k : ℝ) + B) * ((k : ℝ) + B + 1)))
      (e 0 / ((B + 1 - A) * B)) := by
  have hs := summable_div_nat_add he hB
  have hh := recurrence_first_moment_hasSum hs A (B + 1) (by linarith) hgap
    (divided_sequence_recurrence A B hB hrec)
  convert hh using 1
  · funext k
    rw [div_div]
    congr 2
    ring
  · simp only [Nat.cast_zero, zero_add, div_div]
    congr 1
    ring

end KsIndex.PowerArc
