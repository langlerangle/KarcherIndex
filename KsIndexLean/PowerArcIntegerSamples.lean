module

public import KsIndexLean.PowerArcSampleBounds
public import KsIndexLean.PowerArcConvolution

@[expose] public section


/-! Certified approximations at all integer frequencies with frequency-dependent error bounds. -/

namespace KsIndex.PowerArc

lemma g_natAbs (β : ℝ) (k : ℤ) : g β (k.natAbs : ℝ) = g β k := by
  cases k with
  | ofNat n => simp
  | negSucc n => simpa only [Int.natAbs_negSucc, Int.cast_negSucc, Nat.cast_add,
      Nat.cast_one, Nat.cast_succ] using (g_neg β ((n : ℝ) + 1)).symm

noncomputable def integerSampleCenter (B D S : ℤ) (z : ℝ) (k : ℤ) : ℝ :=
  (if k.natAbs % 2 = 0 then 1 else z) *
    (roundedCoefficient B D (k.natAbs % 2 : ℕ) S (k.natAbs / 2) : ℝ) / S

noncomputable def integerSampleError (B D S : ℤ) (z δ : ℝ) (k : ℤ) : ℝ :=
  let n := k.natAbs / 2
  let e := if k.natAbs % 2 = 0 then 0 else δ
  let c := if k.natAbs % 2 = 0 then 1 else z
  |(roundedCoefficient B D (k.natAbs % 2 : ℕ) S n : ℝ) / S| * e +
    |c| * (n * (1 / (S : ℝ))) + (n * (1 / (S : ℝ))) * e

theorem integerSample_bound {B D S : ℤ} (hB : 0 < B) (hD : 0 < D) (hS : 0 < S)
    {z δ : ℝ} (hseed : |g ((B : ℝ) / D) 1 / g ((B : ℝ) / D) 0 - z| ≤ δ) (k : ℤ) :
    |g ((B : ℝ) / D) k / g ((B : ℝ) / D) 0 - integerSampleCenter B D S z k| ≤
      integerSampleError B D S z δ k := by
  have hβ : (0 : ℝ) < (B : ℝ) / D := by positivity
  have hg0 : g ((B : ℝ) / D) 0 ≠ 0 :=
    (g_pos_of_mem_unit hβ (by norm_num) (by norm_num)).ne'
  have hpar : k.natAbs % 2 = 0 ∨ k.natAbs % 2 = 1 := by omega
  have hse : |g ((B : ℝ) / D) (k.natAbs % 2 : ℕ) / g ((B : ℝ) / D) 0 -
      (if k.natAbs % 2 = 0 then 1 else z)| ≤ (if k.natAbs % 2 = 0 then 0 else δ) := by
    rcases hpar with h | h <;> simp only [h]
    · simp [hg0]
    · simpa using hseed
  have hh := rounded_sample_error hB hD (r := (k.natAbs % 2 : ℕ))
    (by positivity) hS hse (k.natAbs / 2)
  have harg : (((k.natAbs % 2 : ℕ) : ℤ) : ℝ) + 2 * ((k.natAbs / 2 : ℕ) : ℝ) =
      (k.natAbs : ℝ) := by
    have he := congrArg (fun n : ℕ => (n : ℝ)) (Nat.mod_add_div k.natAbs 2)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.cast_natCast] using he
  rw [harg, g_natAbs] at hh
  simpa only [integerSampleCenter, integerSampleError, mul_div_assoc] using hh

end KsIndex.PowerArc
