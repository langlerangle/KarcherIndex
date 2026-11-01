module

public import KsIndexLean.SlitPlanarDomain

@[expose] public section


noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- The radial formula is exactly the existing circle reflection, including its value at zero. -/
lemma radialInversion_eq_sigma (z : ℂ) : radialInversion z = KsIndex.Bracket.σ z := by
  rw [KsIndex.Bracket.σ, one_div, Complex.inv_def]
  simp [radialInversion, Complex.normSq_eq_norm_sq, Complex.real_smul, mul_comm]

lemma joinedDiskValue_sigma_formula (u v : ComplexH1) (c : ℂ) (z : ℂ) :
    joinedDiskValue u v c z =
      if ‖z‖ ≤ 1 then valueCLM u z else c • valueCLM v (KsIndex.Bracket.σ z) := by
  simp only [joinedDiskValue, radialJoin, radialInversion_eq_sigma]

/-- Swapping disks is reflected coordinate change off the seam, with its exclusions explicit. -/
lemma ordinary_join_reflection (u v : ComplexH1) {z : ℂ}
    (hz : z ≠ 0) (hn : ‖z‖ ≠ 1) :
    joinedDiskValue u v 1 (KsIndex.Bracket.σ z) = joinedDiskValue v u 1 z := by
  simp only [joinedDiskValue_sigma_formula, one_smul, KsIndex.Bracket.σ_σ]
  rcases lt_or_gt_of_ne hn with h | h
  · rw [ite_eq_right (KsIndex.Bracket.not_norm_σ_le hz h), ite_eq_left h.le]
  · have hi : ‖KsIndex.Bracket.σ z‖ ≤ 1 := by
      rw [KsIndex.Bracket.norm_σ]
      exact (inv_le_one₀ (norm_pos_iff.mpr hz)).mpr h.le
    rw [ite_eq_left hi, ite_eq_right (not_le.mpr h)]

end KsIndex.Trace
