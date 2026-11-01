module

public import KsIndexLean.KarcherPlanePreimage
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section


/-! The distinguished radial curves attain every horizontal distance. -/
noncomputable section
namespace KsIndex.KarcherData
open Set

lemma one_sub_pow_le_mul {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    1 - s ^ n ≤ (n : ℝ) * (1 - s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have hp := (pow_le_one₀ hs hs1 : s ^ n ≤ 1)
    nlinarith

lemma lambdaR_log_lower {k : ℕ} (hk : 2 ≤ k) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s < 1) : 1 / (2 * (1 - s)) ≤ lambdaR k s := by
  have hd : 0 < 1 - s ^ (2 * k) := sub_pos.mpr (pow_lt_one₀ hs hs1 (by omega))
  have hb := one_sub_pow_le_mul hs hs1.le (2 * k)
  have hp := pow_nonneg hs (2 * k - 2)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  unfold lambdaR
  apply (div_le_div_iff₀ (by positivity) hd).mpr
  push_cast at hb
  nlinarith [mul_nonneg (mul_nonneg hk0.le hp) (sub_nonneg.mpr hs1.le)]

lemma bigL_log_lower {k : ℕ} (hk : 2 ≤ k) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) : -Real.log (1 - r) / 2 ≤ bigL k r := by
  have hc : ContinuousOn (fun s : ℝ => 1 / (2 * (1 - s))) (uIcc 0 r) := by
    apply continuousOn_const.div
      (continuous_const.mul (continuous_const.sub continuous_id)).continuousOn
    intro s hs
    rw [uIcc_of_le hr] at hs
    have : s < 1 := lt_of_le_of_lt hs.2 hr1
    exact mul_ne_zero (by norm_num) (ne_of_gt (sub_pos.mpr this))
  have hi : IntervalIntegrable (fun s : ℝ => 1 / (2 * (1 - s))) MeasureTheory.volume 0 r :=
    hc.intervalIntegrable
  have he : (∫ s in (0 : ℝ)..r, 1 / (2 * (1 - s))) = -Real.log (1 - r) / 2 := by
    have hd : ∀ s ∈ uIcc 0 r,
        HasDerivAt (fun s : ℝ => -Real.log (1 - s) / 2) (1 / (2 * (1 - s))) s := by
      intro s hs
      rw [uIcc_of_le hr] at hs
      have hn : 1 - s ≠ 0 := ne_of_gt (sub_pos.mpr (lt_of_le_of_lt hs.2 hr1))
      convert! (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).log hn).neg.div_const 2
        using 1
      simp only [Pi.sub_apply, id_eq]
      field_simp [hn]
      ring
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [← he]
  exact intervalIntegral.integral_mono_on hr hi
    (lambdaR_continuousOn hk hr hr1).intervalIntegrable
    (fun s hs => lambdaR_log_lower hk hs.1 (lt_of_le_of_lt hs.2 hr1))

/-- The radial length covers the entire nonnegative real axis, before the
puncture is reached. Only a one-dimensional integral estimate is used. -/
theorem bigL_surjective_nonneg {k : ℕ} (hk : 2 ≤ k) {L : ℝ} (hL : 0 ≤ L) :
    ∃ r ∈ Ico (0 : ℝ) 1, bigL k r = L := by
  let b := 1 - Real.exp (-2 * (L + 1))
  have hb0 : 0 ≤ b := by
    dsimp [b]
    have he : Real.exp (-2 * (L + 1)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hb1 : b < 1 := by dsimp [b]; linarith [Real.exp_pos (-2 * (L + 1))]
  have hLb : L ≤ bigL k b := by
    have hh := bigL_log_lower hk hb0 hb1
    have he : 1 - b = Real.exp (-2 * (L + 1)) := by dsimp [b]; ring
    rw [he, Real.log_exp] at hh
    linarith
  have hc : ContinuousOn (bigL k) (Icc 0 b) := by
    have hint : MeasureTheory.IntegrableOn (lambdaR k) (uIcc 0 b) MeasureTheory.volume :=
      (lambdaR_continuousOn hk hb0 hb1).integrableOn_compact isCompact_uIcc
    have hh := intervalIntegral.continuousOn_primitive_interval hint
    rw [uIcc_of_le hb0] at hh
    exact hh
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc hb0 hc
    (show L ∈ Icc (bigL k 0) (bigL k b) from ⟨by simpa [bigL] using hL, hLb⟩)
  exact ⟨r, ⟨hr.1, lt_of_le_of_lt hr.2 hb1⟩, he⟩

end KsIndex.KarcherData
