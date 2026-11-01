module

public import KsIndexLean.StieltjesRationalMoments

@[expose] public section


/-! A rational remainder bound for the first two Stieltjes expansion terms. -/

namespace KsIndex.PowerArc

theorem stieltjes_two_term_identity (x B z : ℝ)
    (hB : x + B ≠ 0) (hB1 : x + B + 1 ≠ 0) (hz : x + z ≠ 0) :
    1 / (x + z) - 1 / (x + B) - (B - z) / ((x + B) * (x + B + 1)) =
      (B - z) * (B + 1 - z) / ((x + B) * (x + B + 1) * (x + z)) := by
  field_simp
  ring

/-- A bound on the endpoint ratio controls the remainder for the entire
positive half-line. -/
theorem stieltjes_two_term_kernel_bound (x B z M : ℝ)
    (hx : 0 ≤ x) (hB : 0 < B) (hz : 0 < z)
    (hM : 1 ≤ M) (hend : B + 2 ≤ M * z) :
    |1 / (x + z) - 1 / (x + B) - (B - z) / ((x + B) * (x + B + 1))| ≤
      |(B - z) * (B + 1 - z)| * M /
        ((x + B) * (x + B + 1) * (x + B + 2)) := by
  have h0 : 0 < x + B := by positivity
  have h1 : 0 < x + B + 1 := by positivity
  have h2 : 0 < x + B + 2 := by positivity
  have hxz : 0 < x + z := by positivity
  have hden : 0 < (x + B) * (x + B + 1) * (x + B + 2) := by positivity
  have hratio : (x + B + 2) / (x + z) ≤ M := by
    apply (div_le_iff₀ hxz).2
    nlinarith
  rw [stieltjes_two_term_identity x B z h0.ne' h1.ne' hxz.ne', abs_div,
    abs_of_pos (by positivity : 0 < (x + B) * (x + B + 1) * (x + z))]
  have hid : |(B - z) * (B + 1 - z)| / ((x + B) * (x + B + 1) * (x + z)) =
      (|(B - z) * (B + 1 - z)| * ((x + B + 2) / (x + z))) /
        ((x + B) * (x + B + 1) * (x + B + 2)) := by
    field_simp
  rw [hid]
  apply (div_le_div_iff_of_pos_right hden).2
  exact mul_le_mul_of_nonneg_left hratio (abs_nonneg _)

/-- Summing the pointwise remainder bound gives an explicit enclosure, with
the third absolute moment as the only tail input. -/
theorem stieltjes_two_term_tsum_bound {e : ℕ → ℝ} (he : Summable e)
    (A B z M E : ℝ) (hB : 0 < B) (hz : 0 < z)
    (hgap : B - A ≠ 0) (hgap1 : B + 1 - A ≠ 0)
    (hM : 1 ≤ M) (hend : B + 2 ≤ M * z)
    (hrec : ∀ k : ℕ, ((k : ℝ) + B) * e (k + 1) = ((k : ℝ) + A) * e k)
    (hthird : HasSum (fun k : ℕ => |e k| /
      (((k : ℝ) + B) * ((k : ℝ) + B + 1) * ((k : ℝ) + B + 2))) E) :
    |(∑' k : ℕ, e k / ((k : ℝ) + z)) - e 0 / (B - A) -
        (B - z) * (e 0 / ((B + 1 - A) * B))| ≤
      (|(B - z) * (B + 1 - z)| * M) * E := by
  let C := |(B - z) * (B + 1 - z)| * M
  let err : ℕ → ℝ := fun k => e k * (1 / ((k : ℝ) + z) - 1 / ((k : ℝ) + B) -
    (B - z) / (((k : ℝ) + B) * ((k : ℝ) + B + 1)))
  have hpoint (k : ℕ) : |err k| ≤ C * (|e k| /
      (((k : ℝ) + B) * ((k : ℝ) + B + 1) * ((k : ℝ) + B + 2))) := by
    have hh := mul_le_mul_of_nonneg_left
      (stieltjes_two_term_kernel_bound (k : ℝ) B z M (Nat.cast_nonneg k) hB hz hM hend)
      (abs_nonneg (e k))
    dsimp [err]
    rw [abs_mul]
    calc
      _ ≤ |e k| * (|(B - z) * (B + 1 - z)| * M /
          (((k : ℝ) + B) * ((k : ℝ) + B + 1) * ((k : ℝ) + B + 2))) := hh
      _ = _ := by dsimp [C]; ring
  have hmaj := hthird.summable.mul_left C
  have habs : Summable (fun k => |err k|) :=
    hmaj.of_nonneg_of_le (fun k => abs_nonneg (err k)) hpoint
  have hbound : |∑' k, err k| ≤ C * E := by
    calc
      |∑' k, err k| ≤ ∑' k, |err k| := by
        simpa only [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm (f := err) (by simpa only [Real.norm_eq_abs] using habs)
      _ ≤ ∑' k, C * (|e k| /
          (((k : ℝ) + B) * ((k : ℝ) + B + 1) * ((k : ℝ) + B + 2))) :=
        habs.tsum_le_tsum hpoint hmaj
      _ = C * E := (hthird.mul_left C).tsum_eq
  have hs := ((summable_div_nat_add he hz).hasSum.sub
    (recurrence_first_moment_hasSum he A B hB hgap hrec)).sub
      ((recurrence_second_moment_hasSum he A B hB hgap1 hrec).mul_left (B - z))
  have hfun : (fun k : ℕ => e k / ((k : ℝ) + z) - e k / ((k : ℝ) + B) -
      (B - z) * (e k / (((k : ℝ) + B) * ((k : ℝ) + B + 1)))) = err := by
    funext k
    dsimp [err]
    ring
  rw [hfun] at hs
  rw [hs.tsum_eq] at hbound
  exact hbound

end KsIndex.PowerArc
