module

public import KsIndexLean.AlphaInnerPairBounds
public import KsIndexLean.PowerArcShiftedAbsoluteTails

@[expose] public section


/-! Summable error bounds for the paired inner-residual tail after extracting
its signed constant leading term. -/
namespace KsIndex.AlphaResidual

theorem paired_inner_tail_error_bound (n X UA UB : ℝ) (a b : ℕ → ℝ)
    (hX : 1 ≤ X) (hcut : 4*n^2 < X^2)
    (ha : Summable (fun k : ℕ => |a k|/(X+2*k)))
    (hb : Summable (fun k : ℕ => |b k|/(X+2*k)^2))
    (hUA : (∑' k : ℕ, |a k|/(X+2*k)) ≤ UA)
    (hUB : (∑' k : ℕ, |b k|/(X+2*k)^2) ≤ UB) :
    Summable (fun k : ℕ => innerPairA n (X+2*k)*a k + innerPairBError n (X+2*k)*b k) ∧
      |(∑' k : ℕ, (innerPairA n (X+2*k)*a k + innerPairBError n (X+2*k)*b k))| ≤
        innerPairAMajorant n X * UA + innerPairBMajorant n X * UB := by
  let f : ℕ → ℝ := fun k => innerPairA n (X+2*k)*a k + innerPairBError n (X+2*k)*b k
  let A := innerPairAMajorant n X
  let B := innerPairBMajorant n X
  have hp : 0 < 9*X^2-1 := by nlinarith
  have hd : 0 < X^2-4*n^2 := by linarith
  have hA : 0 ≤ A := by dsimp [A, innerPairAMajorant]; positivity
  have hB : 0 ≤ B := by dsimp [B, innerPairBMajorant]; positivity
  have hm (k : ℕ) : |f k| ≤ A*(|a k|/(X+2*k))+B*(|b k|/(X+2*k)^2) := by
    have hx : X ≤ X+2*k := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hpa := inner_pair_a_bound n X (X+2*k) hX hx hcut
    have hpb := inner_pair_b_error_bound n X (X+2*k) hX hx hcut
    calc
      _ ≤ |innerPairA n (X+2*k)*a k|+|innerPairBError n (X+2*k)*b k| := abs_add_le _ _
      _ = |innerPairA n (X+2*k)| *|a k|+|innerPairBError n (X+2*k)| *|b k| := by
        rw [abs_mul, abs_mul]
      _ ≤ (A/(X+2*k))*|a k|+(B/(X+2*k)^2)*|b k| :=
        add_le_add (mul_le_mul_of_nonneg_right hpa (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hpb (abs_nonneg _))
      _ = _ := by ring
  have hmajor := (ha.mul_left A).add (hb.mul_left B)
  have habs : Summable (fun k => |f k|) := hmajor.of_nonneg_of_le (fun k => abs_nonneg _) hm
  have hf : Summable f := habs.of_abs
  refine ⟨hf, ?_⟩
  have hnorm : |∑' k, f k| ≤ ∑' k, |f k| := by
    simpa only [Real.norm_eq_abs] using
      (norm_tsum_le_tsum_norm (f := f) (by simpa only [Real.norm_eq_abs] using habs))
  calc
    _ ≤ ∑' k, |f k| := hnorm
    _ ≤ ∑' k : ℕ, (A*(|a k|/(X+2*k))+B*(|b k|/(X+2*k)^2)) :=
      habs.tsum_le_tsum hm hmajor
    _ = A*(∑' k : ℕ, |a k|/(X+2*k))+B*(∑' k : ℕ, |b k|/(X+2*k)^2) := by
      rw [Summable.tsum_add (ha.mul_left A) (hb.mul_left B), tsum_mul_left, tsum_mul_left]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hUA hA)
      (mul_le_mul_of_nonneg_left hUB hB)

end KsIndex.AlphaResidual
