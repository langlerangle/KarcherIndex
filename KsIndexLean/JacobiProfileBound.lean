module

public import KsIndexLean.NormalizedJacobiModes

@[expose] public section


noncomputable section
namespace KsIndex.Radial

/-- Uniform bound for the rational factor on the disk; no frequency asymptotics. -/
lemma abs_gRad_le {k m : ℕ} (hk : 2 ≤ k) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    |gRad k m r| ≤ (m : ℝ) + kap k := by
  have ht : 0 ≤ r ^ (2 * k - 2) := pow_nonneg hr _
  have ht1 : r ^ (2 * k - 2) ≤ 1 := pow_le_one₀ hr hr1
  have hkap : 0 ≤ kap k := by
    unfold kap
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hd : 0 < r ^ (2 * k - 2) + 1 := by positivity
  rw [abs_le, gRad]
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg m) ht]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg hkap ht]

/-- The normalized radial mode has a frequency-uniform polynomial envelope. -/
lemma abs_phiExt_le {k m : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    |JacobiExtension.phiExt k m r| ≤ (k : ℝ) * r ^ m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hg := abs_gRad_le (m := m) hk hr hr1
  have hmk : (m : ℝ) + kap k ≤ (k : ℝ) * m := by
    unfold kap
    nlinarith [mul_nonneg (sub_nonneg.mpr hk1) (sub_nonneg.mpr hm1)]
  rw [JacobiExtension.phiExt, uRad, abs_div, abs_mul, abs_of_nonneg (pow_nonneg hr _),
    abs_of_pos hm0]
  apply (div_le_iff₀ hm0).mpr
  have h := mul_le_mul_of_nonneg_left (hg.trans hmk) (pow_nonneg hr m)
  nlinarith

end KsIndex.Radial
