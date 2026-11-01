module

public import KsIndexLean.GeneralReflectionRegularity

@[expose] public section


/-! Pointwise reflection and boundary conditions of continuous representatives
of the reflected Sobolev fields. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface KsIndex.FormIndex

lemma fullSeam_mem_iff (z : ℂ) :
    z ∈ seamDomain Set.univ isOpen_univ ↔ 1 / 2 < ‖z‖ ∧ ‖z‖ < 2 := by
  simp [seamDomain, annulusSet, annulusOpens]

lemma sigma_mem_fullSeam {z : ℂ} (hz : z ∈ seamDomain Set.univ isOpen_univ) :
    Bracket.σ z ∈ seamDomain Set.univ isOpen_univ := by
  rw [fullSeam_mem_iff] at hz ⊢
  rw [Bracket.norm_σ]
  have hp : 0 < ‖z‖ := by linarith [hz.1]
  constructor
  · have h := (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2) hp).mpr hz.2
    norm_num at h
    exact h
  · have h := (inv_lt_inv₀ hp (by norm_num : (0 : ℝ) < 1 / 2)).mpr hz.1
    norm_num at h
    exact h

lemma joined_self_reflection (u : ComplexH1) (c : ℂ) (hc : c * c = 1)
    {z : ℂ} (hz : z ≠ 0) (hn : ‖z‖ ≠ 1) :
    joinedDiskValue u u c (Bracket.σ z) = c * joinedDiskValue u u c z := by
  simp only [joinedDiskValue_sigma_formula, Bracket.σ_σ, smul_eq_mul]
  rcases lt_or_gt_of_ne hn with h | h
  · rw [ite_eq_right (Bracket.not_norm_σ_le hz h), ite_eq_left h.le]
  · have hi : ‖Bracket.σ z‖ ≤ 1 := by
      rw [Bracket.norm_σ]
      exact (inv_le_one₀ (norm_pos_iff.mpr hz)).mpr h.le
    rw [ite_eq_left hi, ite_eq_right (not_le.mpr h), ← mul_assoc, hc, one_mul]

/-- AE equality to the reflected field forces the same pointwise symmetry
for every continuous representative, including on the circle. -/
theorem continuous_joined_reflection (u : ComplexH1) (c : ℂ) (hc : c * c = 1)
    {F : ℂ → ℂ}
    (hF : ContinuousOn F (seamDomain Set.univ isOpen_univ : Set ℂ))
    (ha : joinedDiskValue u u c =ᵐ[volume.restrict
      (seamDomain Set.univ isOpen_univ : Set ℂ)] F) :
    ∀ z ∈ seamDomain Set.univ isOpen_univ, F (Bracket.σ z) = c * F z := by
  let Ω := seamDomain Set.univ isOpen_univ
  have he := (ae_restrict_iff' Ω.isOpen.measurableSet).mp ha
  have hp := Spherical.ae_comp_sigma he
  have hn : ∀ᵐ z : ℂ ∂volume, ‖z‖ ≠ 1 := by
    have hnull := Measure.addHaar_sphere volume (0 : ℂ) 1
    simpa only [ae_iff, not_not, Metric.sphere, dist_zero_right] using hnull
  have hae : (fun z => F (Bracket.σ z)) =ᵐ[volume.restrict (Ω : Set ℂ)]
      (fun z => c * F z) := by
    filter_upwards [he.filter_mono (ae_mono Measure.restrict_le_self),
      hp.filter_mono (ae_mono Measure.restrict_le_self),
      hn.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem Ω.isOpen.measurableSet] with z he hp hn hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (by
      have := (fullSeam_mem_iff z).mp hz
      linarith [this.1])
    rw [← hp (sigma_mem_fullSeam hz), ← he hz]
    exact joined_self_reflection u c hc hz0 hn
  have hs : ContinuousOn Bracket.σ (Ω : Set ℂ) := by
    intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (by
      have := (fullSeam_mem_iff z).mp hz
      linarith [this.1])
    exact (Bracket.contDiffAt_σ hz0).continuousAt.continuousWithinAt
  exact MeasureTheory.Measure.eqOn_of_ae_eq hae (hF.comp hs (fun _ hz => sigma_mem_fullSeam hz))
    (continuousOn_const.mul hF) (by rw [Ω.isOpen.interior_eq]; exact subset_closure)

/-- Odd reflection forces the Dirichlet boundary value pointwise. -/
theorem odd_joined_boundary_zero (u : ComplexH1) {F : ℂ → ℂ}
    (hF : ContinuousOn F (seamDomain Set.univ isOpen_univ : Set ℂ))
    (ha : joinedDiskValue u u (-1) =ᵐ[volume.restrict
      (seamDomain Set.univ isOpen_univ : Set ℂ)] F)
    {z : ℂ} (hz : ‖z‖ = 1) : F z = 0 := by
  have hm : z ∈ seamDomain Set.univ isOpen_univ := by
    rw [fullSeam_mem_iff, hz]; norm_num
  have h := continuous_joined_reflection u (-1) (by norm_num) hF ha z hm
  rw [Bracket.σ_self hz, neg_one_mul] at h
  linear_combination (1 / 2 : ℂ) * h

/-- Even reflection forces zero Euclidean radial derivative on the circle.
Conformal rescaling does not change this homogeneous Neumann condition. -/
theorem even_joined_boundary_normal_zero (u : ComplexH1) {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (seamDomain Set.univ isOpen_univ : Set ℂ))
    (ha : joinedDiskValue u u 1 =ᵐ[volume.restrict
      (seamDomain Set.univ isOpen_univ : Set ℂ)] F)
    {z : ℂ} (hz : ‖z‖ = 1) : fderiv ℝ F z z = 0 := by
  have hm : z ∈ seamDomain Set.univ isOpen_univ := by
    rw [fullSeam_mem_iff, hz]; norm_num
  have hsym := continuous_joined_reflection u 1 (by norm_num) hF.continuousOn ha
  have he : (F ∘ Bracket.σ) =ᶠ[nhds z] F := by
    apply Filter.eventuallyEq_of_mem ((seamDomain Set.univ isOpen_univ).isOpen.mem_nhds hm)
    intro w hw
    simpa only [Function.comp_apply, one_mul] using hsym w hw
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hd : DifferentiableAt ℝ F z :=
    (hF.contDiffAt ((seamDomain Set.univ isOpen_univ).isOpen.mem_nhds hm)).differentiableAt
      (by simp)
  have hds : DifferentiableAt ℝ F (Bracket.σ z) := by rwa [Bracket.σ_self hz]
  have hσ : DifferentiableAt ℝ Bracket.σ z :=
    (SigmaDeriv.hasFDerivAt_sigmaR hz0).differentiableAt
  have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L z) he.fderiv_eq
  rw [fderiv_comp z hds hσ, ContinuousLinearMap.comp_apply,
    Bracket.σ_self hz] at h
  have hr : fderiv ℝ Bracket.σ z z = -z := SigmaDeriv.fderiv_sigmaR_radial hz
  rw [hr, map_neg] at h
  linear_combination (-1 / 2 : ℂ) * h

/-- Classical reflected representative with its pointwise Dirichlet condition. -/
theorem dirichlet_radical_reflection_boundary {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1) (hzero : u ∈ zeroTraceDomain Set.univ)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1, v ∈ zeroTraceDomain Set.univ ⊓
      weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ F : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F
        (seamDomain Set.univ isOpen_univ : Set ℂ) ∧
      joinedDiskValue u u (-1) =ᵐ[volume.restrict
        (seamDomain Set.univ isOpen_univ : Set ℂ)] F ∧
      (∀ z ∈ seamDomain Set.univ isOpen_univ,
        laplacian F z + (potV k z : ℂ) * F z = 0) ∧
      ∀ z : ℂ, ‖z‖ = 1 → F z = 0 := by
  obtain ⟨F, hF, ha, hPDE⟩ := dirichlet_radical_reflection_classical hk j u hzero hu hQ
  exact ⟨F, hF, ha, hPDE, fun _ hz => odd_joined_boundary_zero u hF.continuousOn ha hz⟩

/-- Classical reflected representative with its pointwise Neumann condition. -/
theorem neumann_radical_reflection_boundary {k : ℕ} (hk : 2 ≤ k) (j : ℕ)
    (u : ComplexH1)
    (hu : u ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j))
    (hQ : ∀ v : ComplexH1,
      v ∈ weakCharacterDomain (-(2 * Real.pi) / k) (zeta k ^ j) →
      weakJacobi (surfacePotential k) u v = 0) :
    ∃ F : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) F
        (seamDomain Set.univ isOpen_univ : Set ℂ) ∧
      joinedDiskValue u u 1 =ᵐ[volume.restrict
        (seamDomain Set.univ isOpen_univ : Set ℂ)] F ∧
      (∀ z ∈ seamDomain Set.univ isOpen_univ,
        laplacian F z + (potV k z : ℂ) * F z = 0) ∧
      ∀ z : ℂ, ‖z‖ = 1 → fderiv ℝ F z z = 0 := by
  obtain ⟨F, hF, ha, hPDE⟩ := neumann_radical_reflection_classical hk j u hu hQ
  exact ⟨F, hF, ha, hPDE, fun _ hz => even_joined_boundary_normal_zero u hF ha hz⟩

end KsIndex.Trace
