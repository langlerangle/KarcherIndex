module

public import KsIndexLean.AlphaTrialInnerTail
public import KsIndexLean.PowerArcScaledAbsoluteTails

@[expose] public section


/-! Finite endpoint bounds for the two weighted trial-family tails. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open PowerArc

lemma family_weighted_tail_bound {ι : Type*} [Fintype ι]
    (β : ℝ) (d : ι → ℤ) (a : ι → ℝ) (T p : ℕ) (U : ι → ℝ)
    (hs : ∀ i, Summable (fun k : ℕ => |g β (2*(T:ℝ)+d i+1+2*k)| /
      (2*(T:ℝ)+1+2*k)^p))
    (hb : ∀ i, (∑' k : ℕ, |g β (2*(T:ℝ)+d i+1+2*k)| /
      (2*(T:ℝ)+1+2*k)^p) ≤ U i) :
    (∑' k : ℕ, |familyConvolution β d a (k+T)|/(2*(T:ℝ)+1+2*k)^p) ≤
      ∑ i, |a i / g β 0| * U i := by
  let M : ℕ → ℝ := fun k => ∑ i, |a i / g β 0| *
    (|g β (2*(T:ℝ)+d i+1+2*k)|/(2*(T:ℝ)+1+2*k)^p)
  have hm : Summable M := summable_sum (fun i _ => (hs i).mul_left _)
  have hpoint (k : ℕ) : |familyConvolution β d a (k+T)| /
      (2*(T:ℝ)+1+2*k)^p ≤ M k := by
    unfold familyConvolution M
    calc
      _ ≤ (∑ i, |a i * (g β (2*((k+T:ℤ):ℝ)+d i+1) / g β 0)|) /
          (2*(T:ℝ)+1+2*k)^p :=
        div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ = _ := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        push_cast
        rw [show 2*((k:ℝ)+T)+d i+1 = 2*(T:ℝ)+d i+1+2*k by ring]
        rw [abs_mul, abs_div, abs_div]
        ring
  have ht := hm.of_nonneg_of_le (fun _ => by positivity) hpoint
  calc
    _ ≤ ∑' k, M k := ht.tsum_le_tsum hpoint hm
    _ = ∑ i, |a i / g β 0| *
        (∑' k : ℕ, |g β (2*(T:ℝ)+d i+1+2*k)|/(2*(T:ℝ)+1+2*k)^p) := by
      dsimp only [M]
      rw [Summable.tsum_finsetSum (fun i _ => (hs i).mul_left _)]
      simp only [tsum_mul_left]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (abs_nonneg _))

/-- Only one endpoint per coefficient remains in the linear-weight estimate. -/
theorem family_linear_tail_endpoints {ι : Type*} [Fintype ι]
    (β : ℝ) (d : ι → ℤ) (a : ι → ℝ) (T : ℕ) (c : ℝ)
    (hβ : 0 < β) (hr : ∀ i, β ≤ 2*(T:ℝ)+d i+1) (hc : 1 ≤ c)
    (hcomp : ∀ i, 2*(T:ℝ)+d i+1+β+2 ≤ c*(2*(T:ℝ)+1)) :
    (∑' k : ℕ, |familyConvolution β d a (k+T)|/(2*(T:ℝ)+1+2*k)) ≤
      ∑ i, |a i / g β 0| * (c*|g β (2*(T:ℝ)+d i+1)|/(2*(β+1))) := by
  have hh (i : ι) := abs_g_over_scaled_linear_bound β (2*(T:ℝ)+d i+1)
    (2*(T:ℝ)+1) c hβ (hr i) (by positivity) hc (hcomp i)
  simpa only [pow_one] using family_weighted_tail_bound β d a T 1 _
    (fun i => by simpa only [pow_one] using (hh i).1) (fun i => by simpa only [pow_one] using (hh i).2)

/-- The square-weight estimate likewise reduces to a finite endpoint sum. -/
theorem family_square_tail_endpoints {ι : Type*} [Fintype ι]
    (β : ℝ) (d : ι → ℤ) (a : ι → ℝ) (T : ℕ) (c : ℝ)
    (hβ : 0 < β) (hr : ∀ i, β ≤ 2*(T:ℝ)+d i+1) (hc : 1 ≤ c)
    (hcomp : ∀ i, 2*(T:ℝ)+d i+1+β+4 ≤ c*(2*(T:ℝ)+1)) :
    (∑' k : ℕ, |familyConvolution β d a (k+T)|/(2*(T:ℝ)+1+2*k)^2) ≤
      ∑ i, |a i / g β 0| *
        (c^2*|g β (2*(T:ℝ)+d i+1)|/(2*(β+2)*(2*(T:ℝ)+d i+1+β+2))) := by
  have hh (i : ι) := abs_g_over_scaled_square_bound β (2*(T:ℝ)+d i+1)
    (2*(T:ℝ)+1) c hβ (hr i) (by positivity) hc (hcomp i)
  exact family_weighted_tail_bound β d a T 2 _ (fun i => (hh i).1) (fun i => (hh i).2)

end KsIndex.AlphaRemarkTrial
