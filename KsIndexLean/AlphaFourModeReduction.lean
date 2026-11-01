module

public import KsIndexLean.AlphaFourModeCertificate

@[expose] public section


/-! Full-domain lower bound retaining the four lowest transformed frequencies. -/
noncomputable section
namespace KsIndex.AlphaFourMode
open CircleQ SIsometry

def retainedModes : Finset ℤ := {-2,-1,0,1}

lemma sigM_ge_twelve {m : ℤ} (hm : m ∉ retainedModes) : 12 ≤ sigM m := by
  have ha : (14:ℝ) ≤ |6*(m:ℝ)+4| := by
    have hi : m ≤ -3 ∨ 2 ≤ m := by simp only [retainedModes, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hm; omega
    rcases hi with hi | hi
    · have hr : (m:ℝ) ≤ -3 := by exact_mod_cast hi
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hr : (2:ℝ) ≤ m := by exact_mod_cast hi
      rw [abs_of_nonneg (by linarith)]
      linarith
  rw [sigM, ← sq_abs, le_div_iff₀ (by linarith : (0 : ℝ) < |6 * (m : ℝ) + 4|)]
  nlinarith

/-- Capping the positive symbol at 12 leaves only four explicit corrections.
This holds on the entire admissible domain, without Fourier truncation. -/
theorem four_mode_momentum_bound {u : ℤ → ℂ} (hu : MemDom u) :
    12 * normSq u - ∑ m ∈ retainedModes, (12-sigM m)*‖convS u m‖^2 ≤
      ∑' m : ℤ, sigM m * ‖convS u m‖^2 := by
  let f : ℤ → ℝ := fun m => if m ∈ retainedModes then (12-sigM m)*‖convS u m‖^2 else 0
  have hf : Summable f := summable_of_ne_finset_zero (s := retainedModes)
    (fun m hm => by simp [f, hm])
  have hv : (∑' m, f m) = ∑ m ∈ retainedModes, (12-sigM m)*‖convS u m‖^2 := by
    rw [tsum_eq_sum (s := retainedModes) (fun m hm => by simp [f, hm])]
    apply Finset.sum_congr rfl
    intro m hm
    simp [f, hm]
  have hs := summable_convS_sq (summable_normSq hu.1)
  have hp : ∀ m : ℤ, 12*‖convS u m‖^2-f m ≤ sigM m*‖convS u m‖^2 := by
    intro m
    by_cases hm : m ∈ retainedModes
    · simp [f, hm]
      ring_nf
      exact le_rfl
    · simp only [f]
      rw [ite_eq_right hm, sub_zero]
      exact mul_le_mul_of_nonneg_right (sigM_ge_twelve hm) (sq_nonneg _)
  have hh := ((hs.mul_left 12).sub hf).tsum_le_tsum hp (summable_sigM_mul hu.2)
  rw [(hs.mul_left 12).tsum_sub hf, tsum_mul_left, tsum_convS_sq_eq_normSq hu, hv] at hh
  exact hh

end KsIndex.AlphaFourMode
