module

public import KsIndexLean.PureBoundaryClassicalEquivalence
public import KsIndexLean.NullityRadical
public import KsIndexLean.GeneralDirichletPositivity

@[expose] public section


/-! Pure reflection sectors of actual bounded disk-chain Jacobi fields
have smooth representatives across the marked circle points. Values assigned
at punctures by the normalized chain carrier are not identified with limits. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.NullityDecomp
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Surface KsIndex.SurfaceSym KsIndex.FormIndex

/-- The dirichlet reflection sector extends classically through the circle punctures. -/
theorem dirichlet_sector_classical_extension {k r : ℕ} (hk : 2 ≤ k)
    (W : boundedJacobiSector k r 1 1) :
    ∃ H : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball 0 2) ∧
      EqOn ((uncurryE 2).symm W.val 0) H (WeakH1.disk : Set ℂ) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 2, laplacian H z + (potV k z : ℂ) * H z = 0) ∧
      (∀ z : ℂ, ‖z‖ = 1 → H z = 0) ∧
      (∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖H z‖ ≤ C) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        H (planeRotation (-(2 * Real.pi) / k) z) = (zeta k ^ r) * H z := by
  let u := sectorRestrictFun hk W
  have hu := sectorRestrict_char_mem hk W
  have hd : u ∈ zeroTraceDomain Set.univ := by
    have h := sectorRestrict_mem hk (by decide) (by decide) W
    change u ∈ mixedCharacterDomain k r false false at h
    rw [mixedDD_eq_fullDirichletCharacter (by omega)] at h
    exact h.1
  have hQ : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ r) →
      weakJacobi (surfacePotential k) u v = 0 := by
    intro v hv
    have hm : v ∈ mixedCharacterDomain k r false false := by
      rwa [mixedDD_eq_fullDirichletCharacter (by omega)]
    exact sector_weakJacobi_zero hk (by decide) (by decide) W ⟨v, hm⟩
  obtain ⟨H, hH, ha, hP, hBC, hB, hchar⟩ := dirichlet_radical_classical_character hk r u hd hu hQ
  refine ⟨H, hH, ?_, hP, hBC, hB, hchar⟩
  apply Measure.eqOn_open_of_ae_eq ((sectorRestrictFun_value hk W).symm.trans ha)
    WeakH1.disk.isOpen
  · exact ((sector_field_mem W.property).1.1 0).continuousOn
  · exact hH.continuousOn.mono (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2))

/-- The neumann reflection sector extends classically through the circle punctures. -/
theorem neumann_sector_classical_extension {k r : ℕ} (hk : 2 ≤ k)
    (W : boundedJacobiSector k r 0 0) :
    ∃ H : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball 0 2) ∧
      EqOn ((uncurryE 2).symm W.val 0) H (WeakH1.disk : Set ℂ) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 2, laplacian H z + (potV k z : ℂ) * H z = 0) ∧
      (∀ z : ℂ, ‖z‖ = 1 → fderiv ℝ H z z = 0) ∧
      (∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖H z‖ ≤ C) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        H (planeRotation (-(2 * Real.pi) / k) z) = (zeta k ^ r) * H z := by
  let u := sectorRestrictFun hk W
  have hu := sectorRestrict_char_mem hk W
  have hQ : ∀ v : ComplexH1,
      v ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ r) →
      weakJacobi (surfacePotential k) u v = 0 := by
    intro v hv
    have hm : v ∈ mixedCharacterDomain k r true true :=
      ⟨(mixedTraceDomain_NN k).symm ▸ Submodule.mem_top, hv⟩
    exact sector_weakJacobi_zero hk (by decide) (by decide) W ⟨v, hm⟩
  obtain ⟨H, hH, ha, hP, hBC, hB, hchar⟩ := neumann_radical_classical_character hk r u hu hQ
  refine ⟨H, hH, ?_, hP, hBC, hB, hchar⟩
  apply Measure.eqOn_open_of_ae_eq ((sectorRestrictFun_value hk W).symm.trans ha)
    WeakH1.disk.isOpen
  · exact ((sector_field_mem W.property).1.1 0).continuousOn
  · exact hH.continuousOn.mono (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2))

end KsIndex.NullityDecomp
