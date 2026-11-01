module

public import KsIndexLean.AlphaFourModePairing

@[expose] public section


/-! The finite-dimensional dual vector used in the four-mode form estimate. -/
noncomputable section
namespace KsIndex.AlphaFourMode
open CircleQ

def scale (i : Fin 4) : ℝ := (121/64) * deficit i
lemma scale_pos (i : Fin 4) : 0 < scale i := by
  fin_cases i <;> norm_num [scale, deficit]

def dualVector (z : Fin 4 → ℂ) (i : Fin 4) : ℂ := (scale i : ℂ) * star (z i)
def retainedEnergy (z : Fin 4 → ℂ) : ℝ := ∑ i, scale i * ‖z i‖^2

lemma retainedEnergy_nonneg (z : Fin 4 → ℂ) : 0 ≤ retainedEnergy z :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (scale_pos i).le (sq_nonneg _))

lemma dual_pairing (z : Fin 4 → ℂ) :
    (∑ i, dualVector z i * z i) = (retainedEnergy z : ℂ) := by
  unfold retainedEnergy
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have hn : ‖z i‖^2 = (z i).re^2 + (z i).im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [← Complex.ofReal_pow, hn]
  apply Complex.ext <;> simp [dualVector, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow] <;> ring

lemma dual_diagonal (z : Fin 4 → ℂ) : diagonalEnergy (dualVector z) = retainedEnergy z := by
  unfold diagonalEnergy retainedEnergy
  apply Finset.sum_congr rfl
  intro i hi
  change ‖(scale i : ℂ) * star (z i)‖^2 / scale i = scale i * ‖z i‖^2
  rw [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp [(scale_pos i).ne']

end KsIndex.AlphaFourMode
