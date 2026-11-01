module

/-
Reflection parity, unit length, and smoothness of the explicit Jacobi fields.

For `k ≥ 2`, the horizontal fields `nu1` and `nu2` are even under circle
inversion `σ(w) = 1 / conj(w)`, and `nu3` is odd, at every nonzero `w`.
Their squared norms sum to one, and all three fields are smooth on `ℂ`.
These identities supply parity and boundedness data for the geometric
Jacobi-field construction; that construction is established separately.

Proof contributions are credited to Harmonic's Aristotle (project 8ebbad09,
2026-08-29). This historical attribution does not assert a fresh validation
of the original job records or a build on the current toolchain.
-/
public import Mathlib
public import KsIndexLean.JacobiFields

@[expose] public section


open Complex
open scoped ContDiff

noncomputable section

namespace KsIndex.JacobiFields

/-- The reflection through the unit circle, `σ(w) = 1/w̄`. -/
def σ (w : ℂ) : ℂ := 1 / (starRingEnd ℂ) w

/-! ### Auxiliary lemmas -/

/-- The even power of the norm is a power of `normSq`: `‖w‖^{2k−2} = normSq (w^{k−1})`. -/
private lemma norm_pow_eq_normSq (k : ℕ) (hk : 2 ≤ k) (w : ℂ) :
    ‖w‖ ^ (2 * k - 2) = Complex.normSq (w ^ (k - 1)) := by
  have h : 2 * k - 2 = 2 * (k - 1) := by omega
  rw [h, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul, mul_comm]

/-- `σ(w)^{k−1} = w^{k−1} / |w^{k−1}|²`. -/
private lemma sigma_pow (k : ℕ) {w : ℂ} (hw : w ≠ 0) :
    (σ w) ^ (k - 1) = w ^ (k - 1) / ((Complex.normSq (w ^ (k - 1)) : ℝ) : ℂ) := by
  have hz0 : w ^ (k - 1) ≠ 0 := pow_ne_zero _ hw
  have hc : (starRingEnd ℂ) (w ^ (k - 1)) ≠ 0 := by simpa using hz0
  rw [σ, div_pow, one_pow, ← map_pow, ← Complex.mul_conj]
  field_simp

/-- `‖σ(w)‖^{2k−2} = 1 / ‖w‖^{2k−2}`. -/
private lemma sigma_norm_pow (k : ℕ) (hk : 2 ≤ k) (w : ℂ) :
    ‖σ w‖ ^ (2 * k - 2) = (Complex.normSq (w ^ (k - 1)))⁻¹ := by
  have h : ‖σ w‖ = ‖w‖⁻¹ := by simp [σ]
  rw [h, inv_pow, norm_pow_eq_normSq k hk]

/-- `w ↦ normSq (w^{k−1})` is smooth (it is a real polynomial in `w.re, w.im`). -/
private lemma contDiff_normSq_pow (k : ℕ) :
    ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq (w ^ (k - 1))) := by
  have hf : ContDiff ℝ ∞ (fun w : ℂ => w ^ (k - 1)) := contDiff_id.pow _
  have hre : ContDiff ℝ ∞ (fun w : ℂ => (w ^ (k - 1)).re) := Complex.reCLM.contDiff.comp hf
  have him : ContDiff ℝ ∞ (fun w : ℂ => (w ^ (k - 1)).im) := Complex.imCLM.contDiff.comp hf
  simpa [Complex.normSq_apply] using (hre.mul hre).add (him.mul him)

private lemma denom_ne_zero (k : ℕ) (w : ℂ) : Complex.normSq (w ^ (k - 1)) + 1 ≠ 0 := by
  have := Complex.normSq_nonneg (w ^ (k - 1))
  positivity

/-! ### Seam parity -/

theorem nu1_sigma (k : ℕ) (hk : 2 ≤ k) {w : ℂ} (hw : w ≠ 0) : nu1 k (σ w) = nu1 k w := by
  have hz0 : w ^ (k - 1) ≠ 0 := pow_ne_zero _ hw
  have hr : (0 : ℝ) < Complex.normSq (w ^ (k - 1)) := Complex.normSq_pos.mpr hz0
  unfold nu1
  rw [sigma_norm_pow k hk, sigma_pow k hw, norm_pow_eq_normSq k hk]
  norm_cast
  rw [Complex.div_ofReal_re]
  have h1 : Complex.normSq (w ^ (k - 1)) + 1 > 0 := by linarith
  field_simp
  ring

theorem nu2_sigma (k : ℕ) (hk : 2 ≤ k) {w : ℂ} (hw : w ≠ 0) : nu2 k (σ w) = nu2 k w := by
  have hz0 : w ^ (k - 1) ≠ 0 := pow_ne_zero _ hw
  have hr : (0 : ℝ) < Complex.normSq (w ^ (k - 1)) := Complex.normSq_pos.mpr hz0
  unfold nu2
  rw [sigma_norm_pow k hk, sigma_pow k hw, norm_pow_eq_normSq k hk]
  norm_cast
  rw [Complex.div_ofReal_im]
  have h1 : Complex.normSq (w ^ (k - 1)) + 1 > 0 := by linarith
  field_simp
  ring

theorem nu3_sigma (k : ℕ) (hk : 2 ≤ k) {w : ℂ} (hw : w ≠ 0) : nu3 k (σ w) = -nu3 k w := by
  have hz0 : w ^ (k - 1) ≠ 0 := pow_ne_zero _ hw
  have hr : (0 : ℝ) < Complex.normSq (w ^ (k - 1)) := Complex.normSq_pos.mpr hz0
  unfold nu3
  rw [sigma_norm_pow k hk, norm_pow_eq_normSq k hk]
  norm_cast
  have h1 : Complex.normSq (w ^ (k - 1)) + 1 > 0 := by linarith
  field_simp
  ring

/-! ### Unit length -/

theorem nu_normSq (k : ℕ) (hk : 2 ≤ k) (w : ℂ) :
    ‖nu1 k w‖ ^ 2 + ‖nu2 k w‖ ^ 2 + ‖nu3 k w‖ ^ 2 = 1 := by
  unfold nu1 nu2 nu3
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [norm_pow_eq_normSq k hk]
  set a := (w ^ (k - 1)).re
  set b := (w ^ (k - 1)).im
  have hn : Complex.normSq (w ^ (k - 1)) = a * a + b * b := Complex.normSq_apply _
  rw [hn]
  have hd : a * a + b * b + 1 > 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
  field_simp
  ring

/-! ### Smoothness on `ℂ` -/

theorem nu1_contDiff (k : ℕ) (hk : 2 ≤ k) : ContDiff ℝ ∞ (nu1 k) := by
  have hf : ContDiff ℝ ∞ (fun w : ℂ => w ^ (k - 1)) := contDiff_id.pow _
  have hre : ContDiff ℝ ∞ (fun w : ℂ => (w ^ (k - 1)).re) := Complex.reCLM.contDiff.comp hf
  have hd : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq (w ^ (k - 1)) + 1) :=
    (contDiff_normSq_pow k).add contDiff_const
  have heq : nu1 k =
      fun w : ℂ => ((2 * (w ^ (k - 1)).re / (Complex.normSq (w ^ (k - 1)) + 1) : ℝ) : ℂ) := by
    funext w; simp only [nu1, norm_pow_eq_normSq k hk w]
  rw [heq]
  exact Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul hre).div hd (denom_ne_zero k))

theorem nu2_contDiff (k : ℕ) (hk : 2 ≤ k) : ContDiff ℝ ∞ (nu2 k) := by
  have hf : ContDiff ℝ ∞ (fun w : ℂ => w ^ (k - 1)) := contDiff_id.pow _
  have him : ContDiff ℝ ∞ (fun w : ℂ => (w ^ (k - 1)).im) := Complex.imCLM.contDiff.comp hf
  have hd : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq (w ^ (k - 1)) + 1) :=
    (contDiff_normSq_pow k).add contDiff_const
  have heq : nu2 k =
      fun w : ℂ => ((2 * (w ^ (k - 1)).im / (Complex.normSq (w ^ (k - 1)) + 1) : ℝ) : ℂ) := by
    funext w; simp only [nu2, norm_pow_eq_normSq k hk w]
  rw [heq]
  exact Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul him).div hd (denom_ne_zero k))

theorem nu3_contDiff (k : ℕ) (hk : 2 ≤ k) : ContDiff ℝ ∞ (nu3 k) := by
  have hd : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq (w ^ (k - 1)) + 1) :=
    (contDiff_normSq_pow k).add contDiff_const
  have hn : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq (w ^ (k - 1)) - 1) :=
    (contDiff_normSq_pow k).sub contDiff_const
  have heq : nu3 k = fun w : ℂ =>
      (((Complex.normSq (w ^ (k - 1)) - 1) / (Complex.normSq (w ^ (k - 1)) + 1) : ℝ) : ℂ) := by
    funext w; simp only [nu3, norm_pow_eq_normSq k hk w]
  rw [heq]
  exact Complex.ofRealCLM.contDiff.comp (hn.div hd (denom_ne_zero k))

end KsIndex.JacobiFields
