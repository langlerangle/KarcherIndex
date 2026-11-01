module

public import KsIndexLean.AlphaLowModeBlock

@[expose] public section


/-! Exact interval partition for assembling independently certified blocks. -/
namespace KsIndex.AlphaRemarkTrial

theorem sum_range_int_window {A : Type*} [AddCommMonoid A]
    (base : ℤ) (L : ℕ) (f : ℤ → A) :
    (∑ i ∈ Finset.range L, f (base+i)) =
      ∑ m ∈ Finset.Ico base (base+L), f m := by
  apply Finset.sum_bij (fun (i : ℕ) _ => base+(i : ℤ))
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Ico]
    omega
  · intro i hi j hj hij
    omega
  · intro m hm
    simp only [Finset.mem_Ico] at hm
    refine ⟨(m-base).toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro i hi
    rfl

theorem sum_range_blocks {A : Type*} [AddCommMonoid A] (f : ℕ → A) (B C : ℕ) :
    (∑ i ∈ Finset.range (B*C), f i) =
      ∑ b ∈ Finset.range B, ∑ i ∈ Finset.range C, f (b*C+i) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]

theorem sum_int_window_blocks {A : Type*} [AddCommMonoid A]
    (base : ℤ) (B C R : ℕ) (f : ℤ → A) :
    (∑ m ∈ Finset.Ico base (base+(B*C+R : ℕ)), f m) =
      (∑ b : Fin B, ∑ i : Fin C, f (base+(b.val*C+i.val : ℕ))) +
      ∑ i : Fin R, f (base+(B*C+i.val : ℕ)) := by
  rw [← sum_range_int_window, Finset.sum_range_add, sum_range_blocks]
  rw [Fin.sum_univ_eq_sum_range
    (fun b => ∑ i : Fin C, f (base+(b*C+i.val : ℕ))) B,
    Fin.sum_univ_eq_sum_range (fun i => f (base+(B*C+i : ℕ))) R]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  exact (Fin.sum_univ_eq_sum_range (fun i => f (base+(b*C+i : ℕ))) C).symm

/-- The same partition expressed as consecutive integer intervals. -/
theorem sum_int_window_intervals {A : Type*} [AddCommMonoid A]
    (base : ℤ) (B C R : ℕ) (f : ℤ → A) :
    (∑ m ∈ Finset.Ico base (base+(B*C+R : ℕ)), f m) =
      (∑ b : Fin B, ∑ m ∈ Finset.Ico (base+(b.val*C : ℕ))
        (base+(b.val*C : ℕ)+C), f m) +
      ∑ m ∈ Finset.Ico (base+(B*C : ℕ)) (base+(B*C : ℕ)+R), f m := by
  rw [sum_int_window_blocks]
  congr 1
  · apply Finset.sum_congr rfl
    intro b hb
    rw [← sum_range_int_window, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    push_cast
    ring
  · rw [← sum_range_int_window, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    push_cast
    ring

/-- Block error certificates assemble without losing or duplicating any window terms. -/
theorem window_blocks_error (base : ℤ) (B C R : ℕ) (f : ℤ → ℝ)
    (a e : Fin (B+1) → ℝ)
    (hb : ∀ b : Fin B,
      |(∑ i : Fin C, f (base+(b.val*C+i.val : ℕ))) - a b.castSucc| ≤ e b.castSucc)
    (hr : |(∑ i : Fin R, f (base+(B*C+i.val : ℕ))) - a (Fin.last B)| ≤
      e (Fin.last B)) :
    |(∑ m ∈ Finset.Ico base (base+(B*C+R : ℕ)), f m) -
      ∑ j : Fin (B+1), a j| ≤ ∑ j : Fin (B+1), e j := by
  have hs := CertifiedApproximation.finite_linear_error
    (Finset.univ : Finset (Fin B)) (fun _ => (1 : ℝ))
    (fun b => ∑ i : Fin C, f (base+(b.val*C+i.val : ℕ)))
    (fun b => a b.castSucc) (fun b => e b.castSucc) (fun b _ => hb b)
  simp only [one_mul, abs_one] at hs
  rw [sum_int_window_blocks, Fin.sum_univ_castSucc a, Fin.sum_univ_castSucc e]
  have h := (abs_add_le _ _).trans (add_le_add hs hr)
  simpa only [add_sub_add_comm] using h

/-- Checked block centers equal the core integer accumulation on the same interval. -/
theorem blockLinearNumerator_eq_core {N L : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) (base n : ℤ) (a : Fin L → ℤ)
    (hc : ∀ i : Fin L, SampleCovered N (2*(base+i.val)+1))
    (ha : ∀ i : Fin L, a i = tableSampleNumerator t (2*(base+i.val)+1)) :
    blockLinearNumerator base n a =
      lowLinearNumerator (Finset.Ico base (base+L)) n := by
  unfold blockLinearNumerator lowLinearNumerator
  rw [← sum_range_int_window base L, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ha i, tableSampleNumerator_eq ht (hc i)]

/-- Checked block radii equal the core rounded error accumulation on the same interval. -/
theorem blockLinearRadius_eq_core {N L : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) (base n : ℤ) (e : Fin L → ℤ)
    (hc : ∀ i : Fin L, SampleCovered N (2*(base+i.val)+1))
    (he : ∀ i : Fin L, e i = tableSampleRadius t (2*(base+i.val)+1)) :
    blockLinearRadius base n e =
      lowLinearRadius (Finset.Ico base (base+L)) n := by
  unfold blockLinearRadius lowLinearRadius
  rw [← sum_range_int_window base L, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [he i, tableSampleRadius_eq ht (hc i)]

end KsIndex.AlphaRemarkTrial
