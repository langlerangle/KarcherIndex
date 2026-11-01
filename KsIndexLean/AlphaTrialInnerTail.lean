module

public import KsIndexLean.AlphaTrialPairedResidual

@[expose] public section


/-! A signed leading-term certificate for the actual residual's inner truncation. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual

def signedFamilyTail (f : ℤ → ℝ) (n : ℤ) (T k : ℕ) : ℝ :=
  (-1 : ℝ)^(((k+T:ℕ):ℤ)-n) * f (k+T)

lemma summable_signedFamilyTail {f : ℤ → ℝ} (hf : Summable f) (n : ℤ) (T : ℕ) :
    Summable (signedFamilyTail f n T) := by
  apply Summable.of_abs
  have hh := hf.abs.comp_injective (fun a b h => by dsimp at h; omega :
    Function.Injective (fun k : ℕ => ((k+T:ℕ):ℤ)))
  simpa only [Function.comp_def, signedFamilyTail, abs_mul, abs_neg_one_zpow, one_mul, Nat.cast_add] using hh

lemma summable_signedFamilyTail_weighted {f : ℤ → ℝ} (hf : Summable f)
    (n : ℤ) (T : ℕ) (p : ℕ) :
    Summable (fun k : ℕ => |signedFamilyTail f n T k| / (2*(T:ℝ)+1+2*k)^p) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun k => ?_)
    (summable_signedFamilyTail hf n T).abs
  have hx : (1 : ℝ) ≤ 2*(T:ℝ)+1+2*k := by nlinarith [Nat.cast_nonneg (α := ℝ) T, Nat.cast_nonneg (α := ℝ) k]
  have hp : (1 : ℝ) ≤ (2*(T:ℝ)+1+2*k)^p := one_le_pow₀ hx
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(2*(T:ℝ)+1+2*k)^p)).mpr
  exact le_mul_of_one_le_right (abs_nonneg _) hp

lemma pairedTransposeTerm_signed (n : ℤ) (T k : ℕ) :
    pairedTransposeTerm n (k+T) = (2/Real.pi) *
      innerPair n (2*(T:ℝ)+1+2*k)
        (signedFamilyTail convolutionA n T k) (signedFamilyTail convolutionB n T k) := by
  rw [pairedTransposeTerm_eq]
  unfold signedFamilyTail innerPair
  push_cast
  rw [show 2*((k:ℝ)+T)+1 = 2*(T:ℝ)+1+2*k by ring]
  ring

/-- The inner tail retains its signed leading contribution. Only the remainder
is bounded in absolute value. UA and UB concern the actual trial families. -/
theorem actual_inner_tail_bound (n : ℤ) (T : ℕ) (UA UB : ℝ)
    (hcut : 4*(n:ℝ)^2 < (2*(T:ℝ)+1)^2)
    (hUA : (∑' k : ℕ, |signedFamilyTail convolutionA n T k| /
      (2*(T:ℝ)+1+2*k)) ≤ UA)
    (hUB : (∑' k : ℕ, |signedFamilyTail convolutionB n T k| /
      (2*(T:ℝ)+1+2*k)^2) ≤ UB) :
    |(∑' k : ℕ, pairedTransposeTerm n (k+T)) -
      (12/Real.pi) * ∑' k : ℕ, signedFamilyTail convolutionB n T k| ≤
      (2/Real.pi) * (innerPairAMajorant n (2*(T:ℝ)+1)*UA +
        innerPairBMajorant n (2*(T:ℝ)+1)*UB) := by
  obtain ⟨ha,hb⟩ := summable_convolution_families
  have hwa := summable_signedFamilyTail_weighted ha n T 1
  simp only [pow_one] at hwa
  have hh := inner_pair_tail_bound n (2*(T:ℝ)+1) UA UB
    (signedFamilyTail convolutionA n T) (signedFamilyTail convolutionB n T)
    (by nlinarith [Nat.cast_nonneg (α := ℝ) T]) hcut hwa (summable_signedFamilyTail_weighted hb n T 2)
    hUA hUB (summable_signedFamilyTail hb n T)
  have he : (∑' k : ℕ, pairedTransposeTerm n (k+T)) = (2/Real.pi) *
      ∑' k : ℕ, innerPair n (2*(T:ℝ)+1+2*k)
        (signedFamilyTail convolutionA n T k) (signedFamilyTail convolutionB n T k) := by
    simp only [pairedTransposeTerm_signed, tsum_mul_left]
  rw [he]
  have hscale := mul_le_mul_of_nonneg_left hh.2 (by positivity : (0:ℝ) ≤ 2/Real.pi)
  have hid : (2/Real.pi) *
      (∑' k : ℕ, innerPair n (2*(T:ℝ)+1+2*k)
        (signedFamilyTail convolutionA n T k) (signedFamilyTail convolutionB n T k)) -
      (12/Real.pi) * (∑' k : ℕ, signedFamilyTail convolutionB n T k) =
      (2/Real.pi) * ((∑' k : ℕ, innerPair n (2*(T:ℝ)+1+2*k)
        (signedFamilyTail convolutionA n T k) (signedFamilyTail convolutionB n T k)) -
        6*(∑' k : ℕ, signedFamilyTail convolutionB n T k)) := by ring
  rw [hid, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2/Real.pi)]
  exact hscale

end KsIndex.AlphaRemarkTrial
