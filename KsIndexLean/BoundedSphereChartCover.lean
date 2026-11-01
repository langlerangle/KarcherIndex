module

public import KsIndexLean.SphericalSlitChartDomain

@[expose] public section


open Set Metric

noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace

lemma sphereChart_eq_southChart_sigma {z : ℂ} (hz : z ≠ 0) :
    sphereChart z = southChart (KsIndex.Bracket.σ z) := by
  have hs : KsIndex.Bracket.σ z ≠ 0 := by simp [KsIndex.Bracket.σ, hz]
  rw [southChart_eq_sigma hs, KsIndex.Bracket.σ_σ]

lemma sigma_norm_lt_two_of_large {z : ℂ} (hz : ¬ ‖z‖ < 2) :
    ‖KsIndex.Bracket.σ z‖ < 2 := by
  have h : 1 < ‖z‖ := lt_of_lt_of_le (by norm_num) (not_lt.mp hz)
  rw [KsIndex.Bracket.norm_σ]
  exact ((inv_lt_one₀ (lt_trans zero_lt_one h)).mpr h).trans (by norm_num)

/-- Every sphere point has a coordinate in one of the two radius-two disks. -/
theorem sphere_bounded_chart_cover (p : Sphere) :
    ∃ z : ℂ, ‖z‖ < 2 ∧ (sphereChart z = p ∨ southChart z = p) := by
  have hp : p ∈ Set.range sphereChart ∪ Set.range southChart := by
    rw [sphere_chart_cover]
    trivial
  rcases hp with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · by_cases h : ‖z‖ < 2
    · exact ⟨z, h, Or.inl rfl⟩
    · have hz : z ≠ 0 := by intro hz; simp [hz] at h
      exact ⟨KsIndex.Bracket.σ z, sigma_norm_lt_two_of_large h,
        Or.inr (sphereChart_eq_southChart_sigma hz).symm⟩
  · by_cases h : ‖z‖ < 2
    · exact ⟨z, h, Or.inr rfl⟩
    · have hz : z ≠ 0 := by intro hz; simp [hz] at h
      exact ⟨KsIndex.Bracket.σ z, sigma_norm_lt_two_of_large h,
        Or.inl (southChart_eq_sigma hz).symm⟩

/-- The exact finite-energy weak seam domains cover the actual slit sphere. -/
theorem slitSphere_bounded_chart_cover (k : ℕ) (p : Sphere) (hp : p ∈ slitSphere k) :
    ∃ z ∈ extendedSeamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1),
      sphereChart z = p ∨ southChart z = p := by
  obtain ⟨z, hz, he⟩ := sphere_bounded_chart_cover p
  have hn : z ∉ KsIndex.Bracket.slit k := by
    rcases he with he | he
    · exact (sphereChart_mem_slitSphere k z).mp (he.symm ▸ hp)
    · exact (southChart_mem_slitSphere k z).mp (he.symm ▸ hp)
  refine ⟨z, ?_, he⟩
  change z ∈ (extendedSeamDomain (boundaryArc k 1) (isOpen_boundaryArc k 1) : Set ℂ)
  rw [extendedSeamDomain_eq_slit_chart]
  exact ⟨by simpa [Metric.mem_ball, dist_zero_right] using hz,
    (sphereChart_mem_slitSphere k z).mpr hn⟩

end KsIndex.Spherical
