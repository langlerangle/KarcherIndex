module

public import KsIndexLean.ComplementarySeamChart

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace

lemma sigma_mem_circle_image_iff (A : Set Circle₁) (z : ℂ) :
    KsIndex.Bracket.σ z ∈ Subtype.val '' A ↔ z ∈ Subtype.val '' A := by
  constructor
  · rintro ⟨w, hw, he⟩
    refine ⟨w, hw, ?_⟩
    have hn : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
    have h := congrArg KsIndex.Bracket.σ he
    simpa only [KsIndex.Bracket.σ_self hn, KsIndex.Bracket.σ_σ] using h
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, (KsIndex.Bracket.σ_self
      (mem_sphere_zero_iff_norm.mp w.property)).symm⟩

/-- The overlap of the two center-containing charts is precisely the seam annulus. -/
lemma extendedSeamDomain_overlap_iff {A : Set Circle₁} (hA : IsOpen A) {z : ℂ}
    (hz : z ≠ 0) :
    (z ∈ extendedSeamDomain A hA ∧
      KsIndex.Bracket.σ z ∈ extendedSeamDomain A hA) ↔ z ∈ seamDomain A hA := by
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hi : ‖z‖⁻¹ < 2 ↔ (1 / 2 : ℝ) < ‖z‖ := by
    rw [inv_lt_comm₀ hp (by norm_num : (0 : ℝ) < 2)]
    norm_num
  change ((z ∈ Metric.ball 0 2 ∧ z ∉ Subtype.val '' Aᶜ) ∧
    (KsIndex.Bracket.σ z ∈ Metric.ball 0 2 ∧
      KsIndex.Bracket.σ z ∉ Subtype.val '' Aᶜ)) ↔
    ((1 / 2 : ℝ) < ‖z‖ ∧ ‖z‖ < 2) ∧ z ∉ Subtype.val '' Aᶜ
  simp only [Metric.mem_ball, dist_zero_right, KsIndex.Bracket.norm_σ,
    sigma_mem_circle_image_iff, hi]
  tauto

end KsIndex.Trace
