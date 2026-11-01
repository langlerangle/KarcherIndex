module

public import KsIndexLean.AlphaInnerPairTails
public import KsIndexLean.CircleQ

@[expose] public section


/-! Exact leading-term extraction for the reflected inner-residual tail.

The signed symmetric tail is retained; only the remaining summable error is
bounded in absolute value.
-/
namespace KsIndex.AlphaResidual

noncomputable def innerPair (n x a b : ℝ) : ℝ :=
  (3*x+1-4/(3*x+1))*(a+b)/(x-2*n) -
    (3*x-1-4/(3*x-1))*(a-b)/(x+2*n)

theorem innerPair_eq (n x a b : ℝ) (hx : 1 ≤ x) (hn : 4*n^2 < x^2) :
    innerPair n x a b = 6*b + (innerPairA n x*a + innerPairBError n x*b) := by
  have hm : x-2*n ≠ 0 := by intro h; nlinarith [sq_nonneg (x+2*n)]
  have hp : x+2*n ≠ 0 := by intro h; nlinarith [sq_nonneg (x-2*n)]
  have hwm : 3*x-1 ≠ 0 := by linarith
  have hwp : 3*x+1 ≠ 0 := by linarith
  have hd : x^2-4*n^2 ≠ 0 := by linarith
  unfold innerPair
  rw [paired_fraction_identity x n _ _ a b hm hp,
    reflected_weight_difference x hwm hwp, reflected_weight_sum x hwm hwp]
  calc
    _ = ((x*(2+8/(9*x^2-1))+2*n*(6*x-24*x/(9*x^2-1)))/(x^2-4*n^2))*a +
        ((x*(6*x-24*x/(9*x^2-1))+2*n*(2+8/(9*x^2-1)))/(x^2-4*n^2))*b := by ring
    _ = _ := by
      rw [paired_other_coefficient, paired_leading_extraction x n hd]
      dsimp [innerPairA, innerPairBError]
      ring

/-- The rational weights are the actual circle symbols at reflected integers. -/
theorem reflected_symbol_innerPair (n t : ℤ) (ht : 0 ≤ t) (a b : ℝ) :
    CircleQ.sigM t*(a+b)/(2*(t:ℝ)+1-2*n) -
      CircleQ.sigM (-t-1)*(a-b)/(2*(t:ℝ)+1+2*n) =
        innerPair n (2*(t:ℝ)+1) a b := by
  have htR : (0:ℝ) ≤ t := by exact_mod_cast ht
  have hp : 0 < 6*(t:ℝ)+4 := by linarith
  have hm : 0 < 6*(t:ℝ)+2 := by linarith
  have hpos : CircleQ.sigM t = 6*(t:ℝ)+4-4/(6*(t:ℝ)+4) := by
    unfold CircleQ.sigM
    rw [abs_of_pos hp]
    field_simp
  have hneg : CircleQ.sigM (-t-1) = 6*(t:ℝ)+2-4/(6*(t:ℝ)+2) := by
    unfold CircleQ.sigM
    push_cast
    rw [show 6*(-(t:ℝ)-1)+4 = -(6*(t:ℝ)+2) by ring, abs_neg, abs_of_pos hm]
    field_simp
  rw [hpos, hneg]
  unfold innerPair
  ring

theorem inner_pair_tail_bound (n X UA UB : ℝ) (a b : ℕ → ℝ)
    (hX : 1 ≤ X) (hcut : 4*n^2 < X^2)
    (ha : Summable (fun k : ℕ => |a k|/(X+2*k)))
    (hb : Summable (fun k : ℕ => |b k|/(X+2*k)^2))
    (hUA : (∑' k : ℕ, |a k|/(X+2*k)) ≤ UA)
    (hUB : (∑' k : ℕ, |b k|/(X+2*k)^2) ≤ UB)
    (hbs : Summable b) :
    Summable (fun k : ℕ => innerPair n (X+2*k) (a k) (b k)) ∧
      |(∑' k : ℕ, innerPair n (X+2*k) (a k) (b k)) - 6*(∑' k, b k)| ≤
        innerPairAMajorant n X*UA + innerPairBMajorant n X*UB := by
  obtain ⟨he, hbound⟩ := paired_inner_tail_error_bound n X UA UB a b hX hcut ha hb hUA hUB
  have heq (k : ℕ) := innerPair_eq n (X+2*k) (a k) (b k)
    (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
    (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  have hs := (hbs.mul_left 6).add he
  have hfun : (fun k : ℕ => innerPair n (X+2*k) (a k) (b k)) =
      (fun k : ℕ => 6*b k + (innerPairA n (X+2*k)*a k + innerPairBError n (X+2*k)*b k)) :=
    funext heq
  rw [hfun]
  refine ⟨hs, ?_⟩
  rw [Summable.tsum_add (hbs.mul_left 6) he, tsum_mul_left]
  simpa only [add_sub_cancel_left] using hbound

end KsIndex.AlphaResidual
