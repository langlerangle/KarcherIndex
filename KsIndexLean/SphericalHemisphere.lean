module

public import KsIndexLean.SphericalCoordinates

@[expose] public section


noncomputable section
namespace KsIndex.Spherical

lemma stereoPoint_third_ne_one (z : ℂ) : stereoPoint z 2 ≠ 1 := by
  have hd : 1 + ‖z‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  change (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2) ≠ 1
  intro h
  have he := (div_eq_iff hd).mp h
  linarith

lemma stereoPoint_equator_iff (z : ℂ) : stereoPoint z 2 = 0 ↔ ‖z‖ = 1 := by
  have hd : 1 + ‖z‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  change (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2) = 0 ↔ ‖z‖ = 1
  rw [div_eq_zero_iff]
  simp only [hd, or_false]
  constructor <;> intro h <;> nlinarith [norm_nonneg z]

lemma stereoPoint_lower_iff (z : ℂ) : stereoPoint z 2 < 0 ↔ ‖z‖ < 1 := by
  have hd : 0 < 1 + ‖z‖ ^ 2 := by positivity
  change (‖z‖ ^ 2 - 1) / (1 + ‖z‖ ^ 2) < 0 ↔ ‖z‖ < 1
  rw [div_lt_iff₀ hd]
  constructor <;> intro h <;> nlinarith [norm_nonneg z]

end KsIndex.Spherical
