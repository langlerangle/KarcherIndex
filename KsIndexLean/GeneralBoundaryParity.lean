module

public import KsIndexLean.GeneralBoundaryDisk
public import KsIndexLean.ClassicalCharacterRepresentative

@[expose] public section


/-! Smooth disk representatives retaining the full odd/even seam identity.
This identity supplies smooth gluing when constructing reflected chain fields. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface KsIndex.FormIndex

/-- Attach the interior representative without losing the reflected seam identity. -/
theorem reflected_disk_representative (k : ℕ) (u : ComplexH1) (c : ℂ)
    (hc : c * c = 1) {f F : ℂ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (WeakH1.disk : Set ℂ))
    (ha : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] f)
    (hfP : ∀ z ∈ (WeakH1.disk : Set ℂ), laplacian f z + (potV k z : ℂ) * f z = 0)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (seamDomain Set.univ isOpen_univ : Set ℂ))
    (hFa : joinedDiskValue u u c =ᵐ[volume.restrict
      (seamDomain Set.univ isOpen_univ : Set ℂ)] F)
    (hFP : ∀ z ∈ seamDomain Set.univ isOpen_univ,
      laplacian F z + (potV k z : ℂ) * F z = 0) :
    ∃ H : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball 0 2) ∧
      valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] H ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 2, laplacian H z + (potV k z : ℂ) * H z = 0) ∧
      (∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖H z‖ ≤ C) ∧
      ∀ z ∈ seamDomain Set.univ isOpen_univ, H (Bracket.σ z) = c * H z := by
  have hm := seam_representative_eq_inner isOpen_univ u u c hF.continuousOn hf.continuousOn hFa ha
  obtain ⟨H, hHs, hHf, hHF, hHP, hB⟩ := glue_disk_seam_classical k f F hf hF hm hfP hFP
  refine ⟨H, hHs, ?_, hHP, hB, ?_⟩
  · filter_upwards [ha, ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with z hz hd
    exact hz.trans (hHf hd).symm
  · intro z hz
    rw [(hHF (Bracket.σ z) (sigma_mem_fullSeam hz)).self_of_nhds,
      (hHF z hz).self_of_nhds]
    exact continuous_joined_reflection u c hc hF.continuousOn hFa z hz

/-- A Dirichlet radical has a smooth odd representative on the full seam collar. -/
theorem dirichlet_radical_reflected_disk {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1) (hzero : u ∈ zeroTraceDomain Set.univ)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ H : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball 0 2) ∧
      valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] H ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 2, laplacian H z + (potV k z : ℂ) * H z = 0) ∧
      (∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖H z‖ ≤ C) ∧
      (∀ z ∈ seamDomain Set.univ isOpen_univ, H (Bracket.σ z) = -H z) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        H (planeRotation (-(2 * Real.pi) / k) z) = (zeta k ^ j) * H z := by
  obtain ⟨f, hf, ha, hfP⟩ := Weq.fullDirichlet_tests_classical hk u
    (generalDirichlet_character_tests_extend (by omega) j u hu hQ)
  obtain ⟨F, hF, hFa, hFP⟩ := dirichlet_radical_reflection_classical hk j u hzero hu hQ
  obtain ⟨H, hH, haH, hP, hB, hr⟩ := reflected_disk_representative k u (-1)
    (by norm_num) hf ha hfP hF hFa hFP
  refine ⟨H, hH, haH, hP, hB, ?_, ?_⟩
  · simpa only [neg_one_mul] using hr
  · exact continuous_closedDisk_representative_character _ _ u hu
      (hH.continuousOn.mono (Metric.closedBall_subset_ball (by norm_num))) haH

/-- A Neumann radical has a smooth even representative on the full seam collar. -/
theorem neumann_radical_reflected_disk {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ H : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball 0 2) ∧
      valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] H ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 2, laplacian H z + (potV k z : ℂ) * H z = 0) ∧
      (∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖H z‖ ≤ C) ∧
      (∀ z ∈ seamDomain Set.univ isOpen_univ, H (Bracket.σ z) = H z) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        H (planeRotation (-(2 * Real.pi) / k) z) = (zeta k ^ j) * H z := by
  obtain ⟨f, hf, ha, hfP⟩ := Weq.fullDirichlet_tests_classical hk u
    (fun v _ => generalNeumann_character_tests_extend (by omega) j u hu hQ v)
  obtain ⟨F, hF, hFa, hFP⟩ := neumann_radical_reflection_classical hk j u hu hQ
  obtain ⟨H, hH, haH, hP, hB, hr⟩ := reflected_disk_representative k u 1
    (by norm_num) hf ha hfP hF hFa hFP
  refine ⟨H, hH, haH, hP, hB, ?_, ?_⟩
  · simpa only [one_mul] using hr
  · exact continuous_closedDisk_representative_character _ _ u hu
      (hH.continuousOn.mono (Metric.closedBall_subset_ball (by norm_num))) haH

end KsIndex.Trace
