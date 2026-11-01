module

public import KsIndexLean.AlphaFourModeTail

@[expose] public section


/-! Full integer-lattice Gram energy and a certified two-sided tail allowance. -/
noncomputable section
namespace KsIndex.AlphaFourMode
open ArcTailIntegral

def gramEnergy (a : Fin 4 → ℂ) (n : ℤ) : ℝ := ‖mixedKernel a n‖^2 / weight n

lemma gramEnergy_nonneg (a : Fin 4 → ℂ) (n : ℤ) : 0 ≤ gramEnergy a n :=
  div_nonneg (sq_nonneg _) (weight_pos n).le

lemma gramEnergy_shift_bound (a : Fin 4 → ℂ) (n : ℕ) (e : ℤ) (he : e = 1 ∨ e = -1) :
    gramEnergy a (e*((n:ℤ)+65)) ≤ (4/5:ℝ)*(∑ i, ‖a i‖^2) * cube ((n:ℝ)+65) := by
  have ha : |((e*((n:ℤ)+65):ℤ):ℝ)| = (n:ℝ)+65 := by
    have heabs : |(e:ℝ)| = 1 := by rcases he with rfl | rfl <;> norm_num
    push_cast
    rw [abs_mul, heabs, one_mul, abs_of_nonneg (by positivity)]
  have hb := mixedKernel_tail_bound a (n := e*((n:ℤ)+65)) (by rw [ha]; have := Nat.cast_nonneg (α := ℝ) n; linarith)
  rw [ha] at hb
  simpa [gramEnergy, cube, div_eq_mul_inv] using hb

lemma gramEnergy_shift_summable (a : Fin 4 → ℂ) (e : ℤ) (he : e = 1 ∨ e = -1) :
    Summable (fun n : ℕ => gramEnergy a (e*((n:ℤ)+65))) := by
  exact ((summable_cube_shift 65).mul_left ((4/5:ℝ)*(∑ i, ‖a i‖^2))).of_nonneg_of_le
    (fun n => gramEnergy_nonneg _ _) (fun n => gramEnergy_shift_bound a n e he)

lemma gramEnergy_shift_tsum_le (a : Fin 4 → ℂ) (e : ℤ) (he : e = 1 ∨ e = -1) :
    (∑' n : ℕ, gramEnergy a (e*((n:ℤ)+65))) ≤ (1/10240:ℝ)*(∑ i, ‖a i‖^2) := by
  have hl := (gramEnergy_shift_summable a e he).tsum_le_tsum
    (fun n => gramEnergy_shift_bound a n e he)
    ((summable_cube_shift 65).mul_left ((4/5:ℝ)*(∑ i, ‖a i‖^2)))
  rw [tsum_mul_left] at hl
  have hm := mul_le_mul_of_nonneg_left cubic_tail_64
    (show 0 ≤ (4/5:ℝ)*(∑ i, ‖a i‖^2) by positivity)
  simp only [cube] at hl
  nlinarith

/-- Split a two-sided integer series into a centered finite window and two tails. -/
lemma integer_sum_split_64 {f : ℤ → ℝ}
    (hp : Summable (fun n : ℕ => f ((n:ℤ)+65)))
    (hn : Summable (fun n : ℕ => f (-((n:ℤ)+65)))) :
    Summable f ∧ (∑' n : ℤ, f n) =
      (∑ n ∈ Finset.range 129, f ((n:ℤ)-64)) +
      (∑' n : ℕ, f ((n:ℤ)+65)) + (∑' n : ℕ, f (-((n:ℤ)+65))) := by
  let g : ℤ → ℝ := fun n => f (n-64)
  have hgp : Summable (fun n : ℕ => g n) := by
    apply (summable_nat_add_iff 129).mp
    simpa [g, Nat.cast_add, show ∀ n:ℤ, n+129-64=n+65 by intro n; ring] using hp
  have hgn : Summable (fun n : ℕ => g (-(n+1))) := by
    convert hn using 1
    funext n
    congr 1
  have hg : Summable g := hgp.of_nat_of_neg_add_one hgn
  have hf : Summable f := by
    have hh := hg.comp_injective (show Function.Injective (fun n : ℤ => n+64) from by
      intro a b h; exact add_right_cancel h)
    simpa [g, Function.comp_def] using hh
  refine ⟨hf, ?_⟩
  have hsum := tsum_of_nat_of_neg_add_one hgp hgn
  have hshift : (∑' n : ℤ, g n) = ∑' n : ℤ, f n := by
    exact (Equiv.subRight (64:ℤ)).tsum_eq f
  rw [hshift, ← hgp.sum_add_tsum_nat_add 129] at hsum
  have hp_eq : (fun n : ℕ => g (↑(n+129))) = (fun n : ℕ => f ((n:ℤ)+65)) := by
    funext n
    apply congrArg f
    push_cast
    ring
  have hn_eq : (fun n : ℕ => g (-(n+1))) = (fun n : ℕ => f (-((n:ℤ)+65))) := by
    funext n
    apply congrArg f
    push_cast
    ring
  rw [hp_eq, hn_eq] at hsum
  exact hsum

/-- Uniform tail allowance for every complex four-vector. -/
theorem gramEnergy_tsum_le_finite (a : Fin 4 → ℂ) :
    (∑' n : ℤ, gramEnergy a n) ≤
      (∑ n ∈ Finset.range 129, gramEnergy a ((n:ℤ)-64)) +
      (1/5120:ℝ)*(∑ i, ‖a i‖^2) := by
  have hp : Summable (fun n : ℕ => gramEnergy a ((n:ℤ)+65)) := by
    simpa using gramEnergy_shift_summable a 1 (Or.inl rfl)
  have hn : Summable (fun n : ℕ => gramEnergy a (-((n:ℤ)+65))) := by
    simpa using gramEnergy_shift_summable a (-1) (Or.inr rfl)
  rw [(integer_sum_split_64 hp hn).2]
  have hpl := gramEnergy_shift_tsum_le a 1 (Or.inl rfl)
  have hnl := gramEnergy_shift_tsum_le a (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at hpl hnl
  linarith

end KsIndex.AlphaFourMode
