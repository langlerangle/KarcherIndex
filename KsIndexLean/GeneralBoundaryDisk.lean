module

public import KsIndexLean.GeneralReflectionBoundary
public import KsIndexLean.SeamRepresentativeCompatibility
public import KsIndexLean.JacobiFamily

@[expose] public section


/-! Gluing the interior disk and reflected boundary representatives on an
open neighborhood of the closed disk. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface KsIndex.FormIndex

/-- Compatible classical disk and seam representatives glue on the radius-two
ball. Local equality retains both the PDE and the actual boundary germ. -/
theorem glue_disk_seam_classical (k : ℕ) (f F : ℂ → ℂ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (WeakH1.disk : Set ℂ))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (seamDomain Set.univ isOpen_univ : Set ℂ))
    (hm : EqOn F f (annulusSet (1 / 2 : ℝ) 1))
    (hfP : ∀ z ∈ (WeakH1.disk : Set ℂ), laplacian f z + (potV k z : ℂ) * f z = 0)
    (hFP : ∀ z ∈ seamDomain Set.univ isOpen_univ,
      laplacian F z + (potV k z : ℂ) * F z = 0) :
    ∃ H : ℂ → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball 0 2) ∧
      EqOn H f (WeakH1.disk : Set ℂ) ∧
      (∀ z ∈ seamDomain Set.univ isOpen_univ, H =ᶠ[nhds z] F) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 2, laplacian H z + (potV k z : ℂ) * H z = 0) ∧
      ∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖H z‖ ≤ C := by
  classical
  let H (z : ℂ) := if ‖z‖ < 1 then f z else F z
  have hHf : EqOn H f (WeakH1.disk : Set ℂ) := by
    intro z hz
    exact ite_eq_left (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hz))
  have hHF : EqOn H F (seamDomain Set.univ isOpen_univ : Set ℂ) := by
    intro z hz
    have hz' := (fullSeam_mem_iff z).mp hz
    by_cases h : ‖z‖ < 1
    · exact (ite_eq_left h).trans (hm ⟨hz'.1, h⟩).symm
    · exact ite_eq_right h
  have heF : ∀ z ∈ seamDomain Set.univ isOpen_univ, H =ᶠ[nhds z] F :=
    fun z hz => Filter.eventuallyEq_of_mem
      ((seamDomain Set.univ isOpen_univ).isOpen.mem_nhds hz) hHF
  have hef : ∀ z ∈ (WeakH1.disk : Set ℂ), H =ᶠ[nhds z] f :=
    fun z hz => Filter.eventuallyEq_of_mem (WeakH1.disk.isOpen.mem_nhds hz) hHf
  have hcases (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 2) :
      z ∈ (WeakH1.disk : Set ℂ) ∨ z ∈ seamDomain Set.univ isOpen_univ := by
    by_cases h : ‖z‖ < 1
    · exact Or.inl (Metric.mem_ball.mpr (by simpa only [dist_zero_right] using h))
    · right
      rw [fullSeam_mem_iff]
      exact ⟨by linarith [not_lt.mp h], by simpa only [Metric.mem_ball, dist_zero_right] using hz⟩
  have hHs : ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball 0 2) := by
    intro z hz
    rcases hcases z hz with hd | hs
    · exact ((hf.contDiffAt (WeakH1.disk.isOpen.mem_nhds hd)).congr_of_eventuallyEq
        (hef z hd)).contDiffWithinAt
    · exact ((hF.contDiffAt ((seamDomain Set.univ isOpen_univ).isOpen.mem_nhds hs)).congr_of_eventuallyEq
        (heF z hs)).contDiffWithinAt
  refine ⟨H, hHs, hHf, heF, ?_, ?_⟩
  · intro z hz
    rcases hcases z hz with hd | hs
    · rw [JacobiFamily.laplacian_congr (hef z hd), (hef z hd).self_of_nhds]
      exact hfP z hd
    · rw [JacobiFamily.laplacian_congr (heF z hs), (heF z hs).self_of_nhds]
      exact hFP z hs
  · exact (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
      (hHs.continuousOn.mono (Metric.closedBall_subset_ball (by norm_num)))

/-- A pure dirichlet character radical has a bounded classical representative
on a neighborhood of the closed disk, with its actual boundary condition. -/
theorem dirichlet_radical_closed_disk {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1) (hzero : u ∈ zeroTraceDomain Set.univ)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ H : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball 0 2) ∧
      valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] H ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 2, laplacian H z + (potV k z : ℂ) * H z = 0) ∧
      (∀ z : ℂ, ‖z‖ = 1 → H z = 0) ∧
      ∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖H z‖ ≤ C := by
  obtain ⟨f, hf, ha, hfP⟩ := Weq.fullDirichlet_tests_classical hk u
    (generalDirichlet_character_tests_extend (by omega) j u hu hQ)
  obtain ⟨F, hF, hFa, hFP, hBC⟩ := dirichlet_radical_reflection_boundary hk j u hzero hu hQ
  have hm := seam_representative_eq_inner isOpen_univ u u (-1) hF.continuousOn hf.continuousOn hFa ha
  obtain ⟨H, hHs, hHf, hHF, hHP, hB⟩ := glue_disk_seam_classical k f F hf hF hm hfP hFP
  refine ⟨H, hHs, ?_, hHP, ?_, hB⟩
  · filter_upwards [ha, ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with z hz hd
    exact hz.trans (hHf hd).symm
  · intro z hz
    have hs : z ∈ seamDomain Set.univ isOpen_univ := by
      rw [fullSeam_mem_iff, hz]; norm_num
    rw [(hHF z hs).self_of_nhds]
    exact hBC z hz

/-- A pure neumann character radical has a bounded classical representative
on a neighborhood of the closed disk, with its actual boundary condition. -/
theorem neumann_radical_closed_disk {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1) 
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ H : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) H (Metric.ball 0 2) ∧
      valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] H ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 2, laplacian H z + (potV k z : ℂ) * H z = 0) ∧
      (∀ z : ℂ, ‖z‖ = 1 → fderiv ℝ H z z = 0) ∧
      ∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖H z‖ ≤ C := by
  obtain ⟨f, hf, ha, hfP⟩ := Weq.fullDirichlet_tests_classical hk u
    (fun v _ => generalNeumann_character_tests_extend (by omega) j u hu hQ v)
  obtain ⟨F, hF, hFa, hFP, hBC⟩ := neumann_radical_reflection_boundary hk j u hu hQ
  have hm := seam_representative_eq_inner isOpen_univ u u 1 hF.continuousOn hf.continuousOn hFa ha
  obtain ⟨H, hHs, hHf, hHF, hHP, hB⟩ := glue_disk_seam_classical k f F hf hF hm hfP hFP
  refine ⟨H, hHs, ?_, hHP, ?_, hB⟩
  · filter_upwards [ha, ae_restrict_mem WeakH1.disk.isOpen.measurableSet] with z hz hd
    exact hz.trans (hHf hd).symm
  · intro z hz
    have hs : z ∈ seamDomain Set.univ isOpen_univ := by
      rw [fullSeam_mem_iff, hz]; norm_num
    rw [(hHF z hs).fderiv_eq]
    exact hBC z hz

end KsIndex.Trace
