module

public import KsIndexLean.GeneralBoundaryDisk
public import KsIndexLean.WeakSmoothCharacter

@[expose] public section


/-! Rotation characters of continuous representatives, including the boundary.
The character is transferred from the actual H¹ rotation action by AE
identification and continuity, without imposing new pointwise hypotheses. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface KsIndex.FormIndex

/-- Every continuous closed-disk representative inherits the character of
its Sobolev class at every point of the closed disk. -/
theorem continuous_closedDisk_representative_character (θ : ℝ) (c : ℂ) (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain θ c) {H : ℂ → ℂ}
    (hH : ContinuousOn H (Metric.closedBall (0 : ℂ) 1))
    (ha : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] H) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, H (planeRotation θ z) = c * H z := by
  have hrot : ContinuousOn (fun z => H (planeRotation θ z)) (Metric.closedBall (0 : ℂ) 1) :=
    hH.comp (planeRotation θ).continuous.continuousOn (by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
      rwa [(planeRotation θ).norm_map])
  have hmul : ContinuousOn (fun z => c * H z) (Metric.closedBall (0 : ℂ) 1) :=
    continuousOn_const.mul hH
  have hsub : (WeakH1.disk : Set ℂ) ⊆ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall
  have hp : EqOn (fun z => H (planeRotation θ z)) (fun z => c * H z)
      (WeakH1.disk : Set ℂ) :=
    continuous_representative_character u θ c hu (hH.mono hsub) ha
  apply hp.of_subset_closure hrot hmul hsub
  change Metric.closedBall (0 : ℂ) 1 ⊆ closure (Metric.ball 0 1)
  rw [closure_ball (0 : ℂ) one_ne_zero]

/-- The bounded classical representative retains the original rotation character. -/
theorem dirichlet_radical_classical_character {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1) (hzero : u ∈ zeroTraceDomain Set.univ)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ H : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball 0 2) ∧
      valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] H ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 2, laplacian H z + (potV k z : ℂ) * H z = 0) ∧
      (∀ z : ℂ, ‖z‖ = 1 → H z = 0) ∧
      (∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖H z‖ ≤ C) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        H (planeRotation (-(2 * Real.pi) / k) z) = (zeta k ^ j) * H z := by
  obtain ⟨H, hH, ha, hP, hBC, hB⟩ := dirichlet_radical_closed_disk hk j u hzero hu hQ
  refine ⟨H, hH, ha, hP, hBC, hB, ?_⟩
  exact continuous_closedDisk_representative_character _ _ u hu
    (hH.continuousOn.mono (Metric.closedBall_subset_ball (by norm_num))) ha

/-- The bounded classical representative retains the original rotation character. -/
theorem neumann_radical_classical_character {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1) 
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ H : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball 0 2) ∧
      valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] H ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 2, laplacian H z + (potV k z : ℂ) * H z = 0) ∧
      (∀ z : ℂ, ‖z‖ = 1 → fderiv ℝ H z z = 0) ∧
      (∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖H z‖ ≤ C) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        H (planeRotation (-(2 * Real.pi) / k) z) = (zeta k ^ j) * H z := by
  obtain ⟨H, hH, ha, hP, hBC, hB⟩ := neumann_radical_closed_disk hk j u hu hQ
  refine ⟨H, hH, ha, hP, hBC, hB, ?_⟩
  exact continuous_closedDisk_representative_character _ _ u hu
    (hH.continuousOn.mono (Metric.closedBall_subset_ball (by norm_num))) ha

end KsIndex.Trace
