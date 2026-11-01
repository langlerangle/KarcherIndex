module

public import KsIndexLean.PowerArcSignedTails

@[expose] public section


/-! Stieltjes sums of sequences satisfying a first-order rational recurrence.

All sums below converge absolutely. The recurrence identity retains the
initial-value term and does not rely on a principal-value interpretation.
-/

namespace KsIndex.PowerArc

lemma summable_div_nat_add {e : ℕ → ℝ} (he : Summable e) {z : ℝ} (hz : 0 < z) :
    Summable (fun k : ℕ => e k / ((k : ℝ) + z)) := by
  apply Summable.of_norm
  apply (he.norm.div_const z).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  have hk : z ≤ (k : ℝ) + z := by linarith [Nat.cast_nonneg (α := ℝ) k]
  simp only [norm_div, Real.norm_eq_abs]
  rw [abs_of_pos (lt_of_lt_of_le hz hk)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hz hk

/-- A summable first-order recurrence induces a difference equation for its
Stieltjes transform on the positive half-line. -/
theorem stieltjes_recurrence {e : ℕ → ℝ} (he : Summable e)
    (A B z : ℝ) (hz : 1 < z)
    (hrec : ∀ k : ℕ, ((k : ℝ) + B) * e (k + 1) = ((k : ℝ) + A) * e k) :
    (A - z) * (∑' k : ℕ, e k / ((k : ℝ) + z)) -
      (B - z) * (∑' k : ℕ, e k / ((k : ℝ) + (z - 1))) =
        -e 0 * (B - 1) / (z - 1) := by
  have hz0 : 0 < z := by linarith
  have hz1 : 0 < z - 1 := by linarith
  have hs0 := summable_div_nat_add he hz0
  have hs1 := summable_div_nat_add he hz1
  let f : ℕ → ℝ := fun k => e k + (B - z) * (e k / ((k : ℝ) + (z - 1)))
  have hf : Summable f := he.add (hs1.mul_left (B - z))
  have hf' : Summable (fun k => f (k + 1)) := (summable_nat_add_iff 1).2 hf
  have htel : (∑' k, f (k + 1)) - (∑' k, f k) = -f 0 := by
    have hh := hf.tsum_eq_zero_add
    linarith
  have hstep (k : ℕ) :
      (A - z) * (e k / ((k : ℝ) + z)) -
        (B - z) * (e k / ((k : ℝ) + (z - 1))) = f (k + 1) - f k := by
    have hk0 : 0 < (k : ℝ) + z := by positivity
    have hk1 : 0 < (k : ℝ) + (z - 1) := by positivity
    have hh := hrec k
    dsimp [f]
    push_cast
    rw [show (k : ℝ) + 1 + (z - 1) = k + z by ring]
    field_simp
    nlinarith [hh]
  have hsum := ((hs0.hasSum.mul_left (A - z)).sub
    (hs1.hasSum.mul_left (B - z)))
  have hsum' := hf'.hasSum.sub hf.hasSum
  rw [htel] at hsum'
  have hfun := funext hstep
  rw [← hfun] at hsum'
  have hh := hsum.unique hsum'
  rw [hh]
  dsimp [f]
  simp only [Nat.cast_zero, zero_add]
  field_simp
  ring

/-- The demodulated power-arc lattice satisfies the Stieltjes difference
equation with explicit rational parameters. -/
theorem g_stieltjes_recurrence {β r : ℝ} (hβ : 0 < β) (hr : β ≤ r)
    (z : ℝ) (hz : 1 < z) :
    ((r - β) / 2 - z) *
        (∑' k : ℕ, ((-1 : ℝ) ^ k * g β (r + 2 * k)) / ((k : ℝ) + z)) -
      ((r + β + 2) / 2 - z) *
        (∑' k : ℕ, ((-1 : ℝ) ^ k * g β (r + 2 * k)) / ((k : ℝ) + (z - 1))) =
      -g β r * ((r + β + 2) / 2 - 1) / (z - 1) := by
  let e : ℕ → ℝ := fun k => (-1 : ℝ) ^ k * g β (r + 2 * k)
  have he : Summable e := by
    apply Summable.of_abs
    simpa [e, abs_mul, abs_pow] using abs_g_summable hβ hr
  have hrec (k : ℕ) : ((k : ℝ) + (r + β + 2) / 2) * e (k + 1) =
      ((k : ℝ) + (r - β) / 2) * e k := by
    have hh := g_step_two hβ (r + 2 * k)
    dsimp [e]
    rw [pow_succ]
    push_cast
    rw [show r + 2 * ((k : ℝ) + 1) = (r + 2 * k) + 2 by ring]
    linear_combination -((-1 : ℝ) ^ k) / 2 * hh
  simpa [e] using stieltjes_recurrence he ((r - β) / 2) ((r + β + 2) / 2) z hz hrec

end KsIndex.PowerArc
