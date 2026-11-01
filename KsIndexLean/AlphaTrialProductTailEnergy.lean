module

public import KsIndexLean.AlphaTrialTailEnergy
public import KsIndexLean.PowerArcCoefficientTails

@[expose] public section


/-! Energy-tail errors retaining products of the trial coefficients. -/
namespace KsIndex.AlphaRemarkTrial
open PowerArc

noncomputable def tailProductError (r : Fin 25 → ℝ) (c : ℝ) : ℝ :=
  ∑ i, ∑ j, |(coefficient i).re*(coefficient j).re| *
    (|c-3*(exponent j*r i+exponent i*r j)/(exponent i+exponent j)| *
      ((((r i+exponent i)*(g (exponent i) (r i)/g (exponent i) 0))^2/(4*exponent i*r i)+
        ((r j+exponent j)*(g (exponent j) (r j)/g (exponent j) 0))^2/(4*exponent j*r j))/2))

theorem trial_product_tail_bound (r : Fin 25 → ℝ) (c : ℝ) (hr : ∀ i, 1 ≤ r i) :
    |(∑' n : ℕ, (6*n+c)*(∑ i, tailScale i*g (exponent i) (r i+2*n))^2) -
      tailLeading r| ≤ tailProductError r c := by
  have h := coefficient_finite_tail_bound exponent r (fun i => (coefficient i).re)
    c exponent_pos hr
  have hs (n : ℕ) : (∑ i, (coefficient i).re*(g (exponent i) (r i+2*n)/g (exponent i) 0)) =
      ∑ i, tailScale i*g (exponent i) (r i+2*n) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [tailScale]
    ring
  have hl : (∑ i : Fin 25, ∑ j : Fin 25, (coefficient i).re*(coefficient j).re*
      (3*(((r i+exponent i)*(g (exponent i) (r i)/g (exponent i) 0))*
        ((r j+exponent j)*(g (exponent j) (r j)/g (exponent j) 0))/
          (2*(exponent i+exponent j))))) = tailLeading r := by
    rw [tailLeading_eq]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hs] at h
  rw [hl] at h
  exact h

theorem positive_sample_product_tail_bound (K : ℤ) (hK : 7 ≤ K) (c : ℝ) :
    |(∑' n : ℕ, (6*n+c)*sample (K+2*n)^2) -
      tailLeading (fun i => (K+shift i : ℤ))| ≤
      tailProductError (fun i => (K+shift i : ℤ)) c := by
  have hr : ∀ i, (1:ℝ) ≤ (K+shift i : ℤ) := by
    intro i
    have hi := (shift_bounds i).1
    exact_mod_cast (show (1:ℤ) ≤ K+shift i by omega)
  simpa only [sample_positive_tail] using trial_product_tail_bound _ c hr

theorem negative_sample_product_tail_bound (K : ℤ) (hK : 7 ≤ K) (c : ℝ) :
    |(∑' n : ℕ, (6*n+c)*sample (-K-2*n)^2) -
      tailLeading (fun i => (K-shift i : ℤ))| ≤
      tailProductError (fun i => (K-shift i : ℤ)) c := by
  have hr : ∀ i, (1:ℝ) ≤ (K-shift i : ℤ) := by
    intro i
    have hi := (shift_bounds i).2
    exact_mod_cast (show (1:ℤ) ≤ K-shift i by omega)
  simpa only [sample_negative_tail] using trial_product_tail_bound _ c hr

end KsIndex.AlphaRemarkTrial
