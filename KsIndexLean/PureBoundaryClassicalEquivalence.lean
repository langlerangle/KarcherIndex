module

public import KsIndexLean.ClassicalWeakBoundary

@[expose] public section


/-! Exact coordinate-level characterizations of the pure-boundary weak kernels.
The classical side consists of representatives smooth near the closed disk;
identification with punctured geometric half-period fields is separate. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface KsIndex.FormIndex

/-- The dirichlet character kernel equals its bounded classical representative condition. -/
theorem dirichlet_radical_iff_classical {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j)) :
    (u ∈ zeroTraceDomain Set.univ ∧
      ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ ⊓
        weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
        weakJacobi (surfacePotential k) u v = 0) ↔
    ∃ H : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball 0 2) ∧
      valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] H ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 2, laplacian H z + (potV k z : ℂ) * H z = 0) ∧
      (∀ z : ℂ, ‖z‖ = 1 → H z = 0) ∧
      (∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖H z‖ ≤ C) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        H (planeRotation (-(2 * Real.pi) / k) z) = (zeta k ^ j) * H z := by
  constructor
  · rintro ⟨hzero, hQ⟩
    exact dirichlet_radical_classical_character hk j u hzero hu hQ
  · rintro ⟨H, hH, ha, hP, hBC, _⟩
    have hPD : ∀ z ∈ (WeakH1.disk : Set ℂ),
        laplacian H z + ((surfacePotential k).V z : ℂ) * H z = 0 := by
      intro z hz
      exact hP z (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hz)
    obtain ⟨v, hv, hzero, hQ⟩ := neighborhood_dirichlet_weak (surfacePotential k) hH hPD hBC
    have huv : u = v := valueCLM_injective (Lp.ext (ha.trans hv.symm))
    subst u
    exact ⟨hzero, fun w hw => hQ w hw.1⟩

/-- The neumann character kernel equals its bounded classical representative condition. -/
theorem neumann_radical_iff_classical {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j)) :
    (∀ v : ComplexH1, v ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
        weakJacobi (surfacePotential k) u v = 0) ↔
    ∃ H : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball 0 2) ∧
      valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] H ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 2, laplacian H z + (potV k z : ℂ) * H z = 0) ∧
      (∀ z : ℂ, ‖z‖ = 1 → fderiv ℝ H z z = 0) ∧
      (∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖H z‖ ≤ C) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        H (planeRotation (-(2 * Real.pi) / k) z) = (zeta k ^ j) * H z := by
  constructor
  · intro hQ
    exact neumann_radical_classical_character hk j u hu hQ
  · rintro ⟨H, hH, ha, hP, hBC, _⟩
    have hPD : ∀ z ∈ (WeakH1.disk : Set ℂ),
        laplacian H z + ((surfacePotential k).V z : ℂ) * H z = 0 := by
      intro z hz
      exact hP z (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hz)
    obtain ⟨v, hv, hQ⟩ := neighborhood_neumann_weak (surfacePotential k) hH hPD hBC
    have huv : u = v := valueCLM_injective (Lp.ext (ha.trans hv.symm))
    subst u
    exact fun w _ => hQ w

end KsIndex.Trace
