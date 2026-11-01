module

public import KsIndexLean.PowerArcSeedLinear

@[expose] public section


/-! Rational evaluation of integer samples with one shared odd seed. -/
noncomputable section
namespace KsIndex.PowerArc

/-- Rational recurrence evaluation at an integer argument, with the odd seed supplied. -/
def integerSeedValue (β seed : ℝ) (q : ℤ) : ℝ :=
  if q.natAbs % 2 = 0 then normalizedCoefficient β 0 (q.natAbs / 2)
  else seed * normalizedCoefficient β 1 (q.natAbs / 2)

/-- Negative arguments use evenness of the power-arc transform. -/
theorem normalized_g_integer_seed {β : ℝ} (hβ : 0 < β) (q : ℤ) :
    g β (q : ℝ)/g β 0 = integerSeedValue β (g β 1/g β 0) q := by
  have he : g β (q : ℝ) = g β (q.natAbs : ℝ) := by
    cases q with
    | ofNat n => simp
    | negSucc n => simp only [Int.cast_negSucc, Int.natAbs_negSucc];
                   simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] using g_neg β ((n : ℝ)+1)
  rw [he, normalized_g_parity hβ]
  rfl

/-- Separate the constant and odd-seed coefficients before interval evaluation. -/
theorem integerSeedValue_affine (β seed : ℝ) (q : ℤ) :
    integerSeedValue β seed q = integerSeedValue β 0 q +
      seed*(integerSeedValue β 1 q-integerSeedValue β 0 q) := by
  unfold integerSeedValue
  split <;> ring

/-- A shared seed error is charged after summing all signed coefficients. -/
theorem integerSeedValue_sum_error {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (q : ι → ℤ) (β a b : ℝ) :
    |(∑ i ∈ s, c i*integerSeedValue β a (q i)) -
      (∑ i ∈ s, c i*integerSeedValue β b (q i))| =
      |a-b| * |∑ i ∈ s, c i*(integerSeedValue β 1 (q i)-integerSeedValue β 0 (q i))| := by
  rw [← abs_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [integerSeedValue_affine β a, integerSeedValue_affine β b]
  ring

end KsIndex.PowerArc
