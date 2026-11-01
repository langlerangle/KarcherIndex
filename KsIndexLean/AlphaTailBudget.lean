module

public import KsIndexLean.AlphaTrialBudgetAssembly
public import KsIndexLean.AlphaCompensatedGroupEnergy

@[expose] public section


/-! Quantitative inequalities for weighted residual tails. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual PowerArc

/-- A reciprocal cube is bounded by a telescoping difference of reciprocal squares. -/
lemma reciprocal_cube_step {x : ℝ} (hx : 0 < x) :
    1/(x+1)^3 ≤ 1/(2*x^2) - 1/(2*(x+1)^2) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx1 : x+1 ≠ 0 := by positivity
  apply (le_sub_iff_add_le).mpr
  field_simp
  nlinarith [sq_nonneg x]

/-- A cubic tail has an explicit bound without a numerical infinite summation. -/
theorem reciprocal_cube_tail (N : ℕ) (hN : 0 < N) :
    Summable (fun k : ℕ => 1/((N:ℝ)+k+1)^3) ∧
      (∑' k : ℕ, 1/((N:ℝ)+k+1)^3) ≤ 1/(2*(N:ℝ)^2) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hsum (K : ℕ) : (∑ k ∈ Finset.range K, 1/((N:ℝ)+k+1)^3) ≤
      1/(2*(N:ℝ)^2) - 1/(2*((N:ℝ)+K)^2) := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have ht := reciprocal_cube_step (x := (N:ℝ)+K) (by positivity)
      push_cast
      simp only [← add_assoc]
      linarith
  have hb (K : ℕ) : (∑ k ∈ Finset.range K, 1/((N:ℝ)+k+1)^3) ≤
      1/(2*(N:ℝ)^2) := (hsum K).trans (sub_le_self _ (by positivity))
  exact ⟨summable_of_sum_range_le (fun k => by positivity) hb,
    Real.tsum_le_of_sum_range_le (fun k => by positivity) hb⟩

/-- Reindex a strict natural-number tail by its first included index. -/
theorem strict_tail_reindex (f : ℕ → ℝ) (N : ℕ)
    (hf : Summable (fun k : ℕ => f (k+(N+1)))) :
    Summable (fun m : ℕ => if N < m then f m else 0) ∧
      (∑' m : ℕ, if N < m then f m else 0) = ∑' k : ℕ, f (k+(N+1)) := by
  have hshift : (fun k : ℕ => if N < k+(N+1) then f (k+(N+1)) else 0) =
      (fun k : ℕ => f (k+(N+1))) := by
    funext k
    rw [ite_eq_left (by omega)]
  have hs : Summable (fun m : ℕ => if N < m then f m else 0) := by
    rw [← summable_nat_add_iff (N+1), hshift]
    exact hf
  refine ⟨hs, ?_⟩
  have h := hs.sum_add_tsum_nat_add (N+1)
  have hz : (∑ m ∈ Finset.range (N+1), if N < m then f m else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [ite_eq_right (by have := Finset.mem_range.mp hm; omega)]
  rw [hz, zero_add, hshift] at h
  exact h.symm

/-- Explicit summable bound for the strict cubic tail. -/
theorem masked_reciprocal_cube_tail (N : ℕ) (hN : 0 < N) :
    Summable (fun m : ℕ => if N < m then 1/(m:ℝ)^3 else 0) ∧
      (∑' m : ℕ, if N < m then 1/(m:ℝ)^3 else 0) ≤ 1/(2*(N:ℝ)^2) := by
  have h := reciprocal_cube_tail N hN
  have he : (fun k : ℕ => 1/((k+(N+1):ℕ):ℝ)^3) =
      (fun k : ℕ => 1/((N:ℝ)+k+1)^3) := by
    funext k
    push_cast
    ring
  have hs := strict_tail_reindex (fun m => 1/(m:ℝ)^3) N (by rw [he]; exact h.1)
  refine ⟨hs.1, ?_⟩
  rw [hs.2, he]
  exact h.2

/-- Adjustable separation of a homogeneous part and its remainder. -/
lemma weighted_square_split {A W C r η : ℝ} (hA : 0 < A) (hAW : A ≤ W)
    (hη : 0 < η) :
    (A*C+r)^2/A ≤ (1+η)*W*C^2 + (1+1/η)*r^2/A := by
  have hη0 := ne_of_gt hη
  have hy : 2*(A*C)*r ≤ η*(A*C)^2 + (1/η)*r^2 := by
    calc
      2*(A*C)*r ≤ (η^2*(A*C)^2+r^2)/η := by
        apply (le_div_iff₀ hη).2
        nlinarith [sq_nonneg (η*(A*C)-r)]
      _ = η*(A*C)^2+(1/η)*r^2 := by field_simp
  have hreplace : (1+η)*A*C^2 ≤ (1+η)*W*C^2 := by
    gcongr
  rw [div_le_iff₀ hA]
  have he : ((1+η)*W*C^2+(1+1/η)*r^2/A)*A =
      (1+η)*W*C^2*A+(1+1/η)*r^2 := by field_simp
  rw [he]
  have hh := mul_le_mul_of_nonneg_right hreplace hA.le
  nlinarith [hy]

/-- Weighted Cauchy-Schwarz with user-supplied positive scales. -/
lemma group_square_bound {ι : Type*} (p : Finset ι) (c u v : ι → ℝ)
    (hc : ∀ i ∈ p, 0 ≤ c i) (hu : ∀ i ∈ p, 0 < u i) :
    (∑ i ∈ p, c i * |v i|)^2 ≤
      (∑ i ∈ p, c i*u i) * ∑ i ∈ p, c i/u i * v i^2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul p
    (fun i hi => mul_nonneg (hc i hi) (hu i hi).le)
    (fun i hi => mul_nonneg (div_nonneg (hc i hi) (hu i hi).le) (sq_nonneg _))
  intro i hi
  rw [mul_pow, sq_abs]
  have h := ne_of_gt (hu i hi)
  field_simp
  exact le_rfl

/-- Combining finitely many weighted energies without a factor equal to the number of groups. -/
theorem group_energy_bound {ι : Type*} (p : Finset ι) (c u : ι → ℝ)
    (v : ι → ℕ → ℝ) (w : ℕ → ℝ)
    (hc : ∀ i ∈ p, 0 ≤ c i) (hu : ∀ i ∈ p, 0 < u i)
    (hw : ∀ n, 0 ≤ w n)
    (hs : ∀ i ∈ p, Summable (fun n => w n * v i n^2))
    (he : ∀ i ∈ p, (∑' n, w n * v i n^2) ≤ u i^2) :
    Summable (fun n => w n * (∑ i ∈ p, c i*|v i n|)^2) ∧
      (∑' n, w n * (∑ i ∈ p, c i*|v i n|)^2) ≤ (∑ i ∈ p, c i*u i)^2 := by
  have hC : 0 ≤ ∑ i ∈ p, c i*u i :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hc i hi) (hu i hi).le)
  have hb (K : ℕ) : (∑ n ∈ Finset.range K,
      w n*(∑ i ∈ p, c i*|v i n|)^2) ≤ (∑ i ∈ p, c i*u i)^2 := by
    calc
      _ ≤ ∑ n ∈ Finset.range K, (∑ i ∈ p, c i*u i)*
          ∑ i ∈ p, c i/u i*(w n*v i n^2) := by
        apply Finset.sum_le_sum
        intro n hn
        have h := mul_le_mul_of_nonneg_left (group_square_bound p c u (fun i => v i n) hc hu) (hw n)
        have heq : (∑ i ∈ p, c i/u i*(w n*v i n^2)) =
            w n * ∑ i ∈ p, c i/u i*v i n^2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        rw [heq]
        convert h using 1; ring
      _ = (∑ i ∈ p, c i*u i)*∑ i ∈ p, c i/u i*∑ n ∈ Finset.range K, w n*v i n^2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ ≤ (∑ i ∈ p, c i*u i)*∑ i ∈ p, c i/u i*u i^2 := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (hc i hi) (hu i hi).le)
        exact ((hs i hi).sum_le_tsum (Finset.range K)
          (fun n hn => mul_nonneg (hw n) (sq_nonneg _))).trans (he i hi)
      _ = (∑ i ∈ p, c i*u i)^2 := by
        have h : ∑ i ∈ p, c i/u i*u i^2 = ∑ i ∈ p, c i*u i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi0 := ne_of_gt (hu i hi)
          field_simp
        rw [h, pow_two]
  have hn (n : ℕ) : 0 ≤ w n*(∑ i ∈ p, c i*|v i n|)^2 := mul_nonneg (hw n) (sq_nonneg _)
  exact ⟨summable_of_sum_range_le hn hb, Real.tsum_le_of_sum_range_le hn hb⟩

/-- A linear lower bound on the weight preserves cubic decay of the remainder energy. -/
lemma remainder_square_bound {m A κ D : ℝ} (hm : 0 < m) (hA : 5*m ≤ A) :
    (κ*(D/m))^2/A ≤ κ^2*D^2/(5*m^3) := by
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  rw [mul_pow, div_pow, ← mul_div_assoc, div_div]
  have hd : 5*m^3 ≤ m^2*A := by nlinarith [mul_le_mul_of_nonneg_left hA (sq_nonneg m)]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hd

/-- An explicit one-sided scalar budget from a homogeneous weighted-energy bound. -/
theorem one_side_tail_budget (N : ℕ) (hN : 0 < N) (C A : ℕ → ℝ)
    (κ D E η : ℝ) (hη : 0 < η)
    (hAlo : ∀ m, N < m → 5*(m:ℝ) ≤ A m)
    (hAhi : ∀ m, N < m → A m ≤ 6*(m:ℝ)+1)
    (hs : Summable (fun m : ℕ => if N < m then (6*(m:ℝ)+1)*C m^2 else 0))
    (he : (∑' m : ℕ, if N < m then (6*(m:ℝ)+1)*C m^2 else 0) ≤ E) :
    Summable (fun m : ℕ => if N < m then (A m*C m+κ*(D/(m:ℝ)))^2/A m else 0) ∧
      (∑' m : ℕ, if N < m then (A m*C m+κ*(D/(m:ℝ)))^2/A m else 0) ≤
        (1+η)*E+(1+1/η)*κ^2*D^2/(10*(N:ℝ)^2) := by
  let H := fun m : ℕ => if N < m then (6*(m:ℝ)+1)*C m^2 else 0
  let R := fun m : ℕ => if N < m then 1/(m:ℝ)^3 else 0
  let b : ℝ := (1+1/η)*κ^2*D^2/5
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc := masked_reciprocal_cube_tail N hN
  have hm : Summable (fun m => (1+η)*H m+b*R m) :=
    (hs.mul_left (1+η)).add (hc.1.mul_left b)
  have hpoint (m : ℕ) : (if N < m then (A m*C m+κ*(D/(m:ℝ)))^2/A m else 0) ≤
      (1+η)*H m+b*R m := by
    by_cases hn : N < m
    · have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have hA0 : 0 < A m := lt_of_lt_of_le (by positivity) (hAlo m hn)
      have hsplit := weighted_square_split (C := C m) (r := κ*(D/(m:ℝ))) hA0 (hAhi m hn) hη
      have hr := mul_le_mul_of_nonneg_left (remainder_square_bound hm0 (hAlo m hn) (κ := κ) (D := D))
        (show 0 ≤ 1+1/η by positivity)
      simp only [H, R, ite_eq_left hn]
      calc
        _ ≤ (1+η)*(6*(m:ℝ)+1)*C m^2+(1+1/η)*(κ*(D/(m:ℝ)))^2/A m := hsplit
        _ ≤ (1+η)*(6*(m:ℝ)+1)*C m^2+(1+1/η)*(κ^2*D^2/(5*(m:ℝ)^3)) := by
          simpa only [mul_div_assoc, add_comm] using add_le_add_left hr ((1+η)*(6*(m:ℝ)+1)*C m^2)
        _ = _ := by dsimp [b]; ring
    · simp [H, R, hn]
  have hnonneg (m : ℕ) : 0 ≤ (if N < m then (A m*C m+κ*(D/(m:ℝ)))^2/A m else 0) := by
    split_ifs with hn
    · apply div_nonneg (sq_nonneg _)
      exact le_trans (by positivity) (hAlo m hn)
    · exact le_rfl
  have hsum := Summable.of_nonneg_of_le hnonneg hpoint hm
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' m, ((1+η)*H m+b*R m) := hsum.tsum_le_tsum hpoint hm
    _ = (1+η)*(∑' m, H m)+b*(∑' m, R m) := by
      rw [Summable.tsum_add (hs.mul_left _) (hc.1.mul_left _), tsum_mul_left, tsum_mul_left]
    _ ≤ (1+η)*E+b*(1/(2*(N:ℝ)^2)) :=
      add_le_add (mul_le_mul_of_nonneg_left he (by positivity)) (mul_le_mul_of_nonneg_left hc.2 hb)
    _ = _ := by dsimp [b]; ring

/-- Linear lower weight on the positive tail. -/
lemma five_mul_le_sigP_nat (m : ℕ) (hm : 2 ≤ m) : 5*(m:ℝ) ≤ sigP (m:ℤ) := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 < 6*(m:ℝ)+1 := by positivity
  simp only [sigP, Int.cast_natCast, abs_of_pos hp]
  apply (le_div_iff₀ hp).2
  nlinarith

/-- Linear lower weight on the reflected tail. -/
lemma five_mul_le_sigP_neg (m : ℕ) (hm : 2 ≤ m) : 5*(m:ℝ) ≤ sigP (-(m:ℤ)) := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 < 6*(m:ℝ)-1 := by linarith
  have ha : |6*(-(m:ℝ))+1| = 6*(m:ℝ)-1 := by rw [abs_of_neg (by linarith)]; ring
  simp only [sigP, Int.cast_neg, Int.cast_natCast, ha]
  apply (le_div_iff₀ hp).2
  nlinarith

/-- The explicit energy bound supplied by an anchor at the first strict-tail index. -/
def compensatedTailEnergy (β r κ w : ℝ) (N : ℕ) : ℝ :=
  let J : ℝ := N+1
  let C := |compensatedPowerArcGroup β r κ w (N+1)|+
    11*|stieltjesCorrectionD β r κ|/(J+9/2)^3
  let t := 2*J+9-r
  (C^2*((6*J+1)/t))*((t+β)^2/(4*β))

/-- An explicit scalar bound for each masked group energy. -/
theorem compensated_group_strict_tail (β r κ w : ℝ) (N : ℕ)
    (hβ : β = 4323618/10000000 ∨ β = 5676382/10000000)
    (hr : r = 14 ∨ r = 15) (hN : 1023 ≤ N) :
    Summable (fun m : ℕ => if N < m then
      (6*(m:ℝ)+1)*compensatedPowerArcGroup β r κ w m^2 else 0) ∧
    (∑' m : ℕ, if N < m then
      (6*(m:ℝ)+1)*compensatedPowerArcGroup β r κ w m^2 else 0) ≤
      compensatedTailEnergy β r κ w N := by
  have h := compensatedPowerArcGroup_energy β r κ w (N+1) hβ hr (by omega)
  dsimp only at h
  have he : (fun k : ℕ => (6*((k+(N+1):ℕ):ℝ)+1)*
      compensatedPowerArcGroup β r κ w (k+(N+1))^2) =
      (fun k : ℕ => (6*(((N+1)+k:ℕ):ℝ)+1)*
      compensatedPowerArcGroup β r κ w ((N+1)+k)^2) := by
    funext k; rw [Nat.add_comm k]
  have ht := strict_tail_reindex
    (fun m => (6*(m:ℝ)+1)*compensatedPowerArcGroup β r κ w m^2) N
    (by rw [he]; exact h.1)
  refine ⟨ht.1, ?_⟩
  rw [ht.2, he]
  simpa only [compensatedTailEnergy, Nat.cast_add, Nat.cast_one] using h.2

/-- A later strict tail is bounded by the energy certificate at an earlier anchor. -/
theorem compensated_group_tail_mono (β r κ w : ℝ) (J N : ℕ)
    (hβ : β = 4323618/10000000 ∨ β = 5676382/10000000)
    (hr : r = 14 ∨ r = 15) (hJ : 1023 ≤ J) (hJN : J ≤ N) :
    Summable (fun m : ℕ => if N < m then
      (6*(m:ℝ)+1)*compensatedPowerArcGroup β r κ w m^2 else 0) ∧
    (∑' m : ℕ, if N < m then
      (6*(m:ℝ)+1)*compensatedPowerArcGroup β r κ w m^2 else 0) ≤
      compensatedTailEnergy β r κ w J := by
  have hj := compensated_group_strict_tail β r κ w J hβ hr hJ
  have hp (m : ℕ) : (if N < m then
      (6*(m:ℝ)+1)*compensatedPowerArcGroup β r κ w m^2 else 0) ≤
      (if J < m then (6*(m:ℝ)+1)*compensatedPowerArcGroup β r κ w m^2 else 0) := by
    by_cases hm : N < m
    · simp only [ite_eq_left hm, ite_eq_left (lt_of_le_of_lt hJN hm), le_refl]
    · rw [ite_eq_right hm]
      split_ifs <;> positivity
  have hs := Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity) hp hj.1
  exact ⟨hs, (hs.tsum_le_tsum hp hj.1).trans hj.2⟩

end KsIndex.AlphaRemarkTrial
