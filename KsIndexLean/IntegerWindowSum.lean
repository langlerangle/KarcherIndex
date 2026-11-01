module

public import Mathlib

@[expose] public section


/-! Splitting a summable integer series into a finite central window and two tails. -/
namespace KsIndex

/-- The finite window contains exactly the integers from `-N` through `N`. -/
theorem tsum_integer_window (f : ℤ → ℝ) (hf : Summable f) (N : ℕ) :
    (∑' k : ℤ, f k) =
      (∑ n ∈ Finset.range (2*N+1), f ((n:ℤ)-N)) +
      (∑' n : ℕ, f ((n:ℤ)+N+1)) +
      (∑' n : ℕ, f (-((n:ℤ)+N+1))) := by
  let g : ℤ → ℝ := fun n => f (n-N)
  have hg : Summable g := hf.comp_injective (show Function.Injective
      (fun n : ℤ => n-(N:ℤ)) from by intro a b h; dsimp only at h; omega)
  have hp : Summable (fun n : ℕ => g n) := hg.comp_injective
    (show Function.Injective (fun n : ℕ => (n:ℤ)) from by intro a b h; dsimp only at h; omega)
  have hn : Summable (fun n : ℕ => g (-(n+1))) := hg.comp_injective
    (show Function.Injective (fun n : ℕ => -((n:ℤ)+1)) from by intro a b h; dsimp only at h; omega)
  have hsum := tsum_of_nat_of_neg_add_one hp hn
  have hshift : (∑' n : ℤ, g n) = ∑' n : ℤ, f n :=
    (Equiv.subRight (N:ℤ)).tsum_eq f
  rw [hshift, ← hp.sum_add_tsum_nat_add (2*N+1)] at hsum
  have he : (fun n : ℕ => g (↑(n+(2*N+1)))) =
      (fun n : ℕ => f ((n:ℤ)+N+1)) := by
    funext n
    apply congrArg f
    push_cast
    ring
  have he' : (fun n : ℕ => g (-(n+1))) =
      (fun n : ℕ => f (-((n:ℤ)+N+1))) := by
    funext n
    apply congrArg f
    ring
  rw [he, he'] at hsum
  exact hsum

/-- Reindex the central window by its consecutive natural-number indices. -/
theorem sum_range_integer_window (f : ℤ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (2*N+1), f ((n:ℤ)-N)) =
      ∑ k ∈ Finset.Icc (-(N:ℤ)) N, f k := by
  apply Finset.sum_bij (fun (n : ℕ) _ => (n:ℤ)-N)
  · intro n hn
    have h := Finset.mem_range.mp hn
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb h
    omega
  · intro k hk
    have h := Finset.mem_Icc.mp hk
    refine ⟨(k+N).toNat, ?_, ?_⟩
    · apply Finset.mem_range.mpr
      omega
    · omega
  · intro n hn
    rfl

end KsIndex
