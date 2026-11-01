module

public import KsIndexLean.AlphaTrialInnerTail
public import KsIndexLean.PowerArcSignedTails

@[expose] public section


/-! Finite endpoint evaluation of the signed leading inner tail. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open PowerArc CircleQ AlphaResidual

lemma family_signed_tail {ι : Type*} [Fintype ι] (β : ℝ) (d : ι → ℤ)
    (a : ι → ℝ) (T : ℕ) (hβ : 0 < β)
    (hr : ∀ i, 1 ≤ 2*(T:ℝ)+d i+1) (hrβ : ∀ i, β ≤ 2*(T:ℝ)+d i+1) :
    (∑' k : ℕ, (-1 : ℝ)^k * familyConvolution β d a (k+T)) =
      ∑ i, (a i / g β 0) *
        ((2*(T:ℝ)+d i+1+β)*g β (2*(T:ℝ)+d i+1)/(2*β)) := by
  have hs (i : ι) : Summable (fun k : ℕ => (-1 : ℝ)^k *
      g β ((2*(T:ℝ)+d i+1)+2*k)) := by
    apply Summable.of_abs
    simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
      abs_g_summable hβ (hrβ i)
  have he : (fun k : ℕ => (-1 : ℝ)^k * familyConvolution β d a (k+T)) =
      fun k : ℕ => ∑ i, (a i / g β 0) *
        ((-1 : ℝ)^k * g β ((2*(T:ℝ)+d i+1)+2*k)) := by
    funext k
    unfold familyConvolution
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    rw [show 2*((k:ℝ)+T)+d i+1 = (2*(T:ℝ)+d i+1)+2*k by ring]
    ring
  rw [he, Summable.tsum_finsetSum (fun i _ => (hs i).mul_left _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [tsum_mul_left, signed_g_tsum hβ (hr i) (hrβ i)]

/-- Thirteen endpoint values suffice to evaluate the symmetric family's signed tail. -/
def leadingTailB (T : ℕ) : ℝ :=
  ∑ i : Fin 13, ((coefficient (familyIndexB i)).re / g (5676382/10000000) 0) *
    ((2*(T:ℝ)+shift (familyIndexB i)+1+(5676382/10000000))*
      g (5676382/10000000) (2*(T:ℝ)+shift (familyIndexB i)+1)/(2*(5676382/10000000)))

theorem signed_convolutionB_tail_eq (T : ℕ) (hT : 4 ≤ T) :
    (∑' k : ℕ, (-1 : ℝ)^k * convolutionB (k+T)) = leadingTailB T := by
  have ht : (4:ℝ) ≤ T := by exact_mod_cast hT
  apply family_signed_tail (5676382/10000000) _ _ T (by norm_num)
  · intro i
    fin_cases i <;> norm_num [familyIndexB, shift] <;> linarith
  · intro i
    fin_cases i <;> norm_num [familyIndexB, shift] <;> linarith

theorem signedFamilyTail_B_tsum (n : ℤ) (T : ℕ) (hT : 4 ≤ T) :
    (∑' k : ℕ, signedFamilyTail convolutionB n T k) =
      (-1 : ℝ)^((T:ℤ)-n) * leadingTailB T := by
  have he : (fun k : ℕ => signedFamilyTail convolutionB n T k) =
      fun k : ℕ => (-1 : ℝ)^((T:ℤ)-n) * ((-1 : ℝ)^k * convolutionB (k+T)) := by
    funext k
    unfold signedFamilyTail
    rw [show (((k+T:ℕ):ℤ)-n) = ((T:ℤ)-n)+(k:ℤ) by omega,
      zpow_add₀ (by norm_num), zpow_natCast]
    ring
  rw [he, tsum_mul_left, signed_convolutionB_tail_eq T hT]

/-- A finite residual approximation with the exact signed leading tail restored. -/
def correctedResidualCenter (s : ℝ) (n : ℤ) (T : ℕ) : ℝ :=
  sigP n * (trial n).re + s^2 * ((∑ t ∈ Finset.range T, pairedTransposeTerm n t) +
    (12/Real.pi) * (-1 : ℝ)^((T:ℤ)-n) * leadingTailB T)

/-- The remaining error uses only weighted absolute tails of the actual families. -/
theorem realResidual_correctedCenter_bound (s : ℝ) (n : ℤ) (T : ℕ)
    (UA UB : ℝ) (hT : 4 ≤ T) (hcut : 4*(n:ℝ)^2 < (2*(T:ℝ)+1)^2)
    (hUA : (∑' k : ℕ, |signedFamilyTail convolutionA n T k| /
      (2*(T:ℝ)+1+2*k)) ≤ UA)
    (hUB : (∑' k : ℕ, |signedFamilyTail convolutionB n T k| /
      (2*(T:ℝ)+1+2*k)^2) ≤ UB) :
    |realResidual s n - correctedResidualCenter s n T| ≤
      s^2 * (2/Real.pi) * (innerPairAMajorant n (2*(T:ℝ)+1)*UA +
        innerPairBMajorant n (2*(T:ℝ)+1)*UB) := by
  have hh := actual_inner_tail_bound n T UA UB hcut hUA hUB
  rw [signedFamilyTail_B_tsum n T hT] at hh
  have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg s)
  rw [realResidual_finite_paired s n T]
  unfold correctedResidualCenter
  have hid : sigP n * (trial n).re + s^2 *
      ((∑ t ∈ Finset.range T, pairedTransposeTerm n t) +
        ∑' k : ℕ, pairedTransposeTerm n (k+T)) -
      (sigP n * (trial n).re + s^2 * ((∑ t ∈ Finset.range T, pairedTransposeTerm n t) +
        (12/Real.pi) * (-1 : ℝ)^((T:ℤ)-n) * leadingTailB T)) =
      s^2 * ((∑' k : ℕ, pairedTransposeTerm n (k+T)) -
        (12/Real.pi) * ((-1 : ℝ)^((T:ℤ)-n) * leadingTailB T)) := by ring
  rw [hid, abs_mul, abs_of_nonneg (sq_nonneg s)]
  simpa only [mul_assoc] using hm

end KsIndex.AlphaRemarkTrial
