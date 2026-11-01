module

public import KsIndexLean.PaperSlitCharacterCoordinates
public import KsIndexLean.RadialCharacter
public import KsIndexLean.ConstrainedPunctureApproximation

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

lemma paperPhase_norm (α : ℝ) : ‖paperPhase α‖ = 1 := by
  simpa [paperPhase] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * α)

lemma paperCharacter_norm (j : ℕ) : ‖KsIndex.FormIndex.zeta 3 ^ j‖ = 1 := by
  rw [paperCharacter_exp]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Simultaneous radial truncation preserves both the slit phase and rotation class. -/
lemma paperSlit_radial_mem (α : ℝ) (j : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (u : paperSlitCharacterDomain α j) :
    (diskRadial t ht u.val.1, diskRadial t ht u.val.2) ∈
      paperSlitCharacterDomain α j := by
  refine ⟨diskRadial_mem_slitTraceDomain t ht 3 _ (paperPhase_norm α) u.property.1, ?_⟩
  exact ⟨diskRadial_mem_weakCharacterDomain t ht _ _ (paperCharacter_norm j) u.property.2.1,
    diskRadial_mem_weakCharacterDomain t ht _ _ (paperCharacter_norm j) u.property.2.2⟩

/-- Bounded pairs are dense in the actual paper phase/character domain. -/
lemma exists_paperSlit_bounded_approx (α : ℝ) (j : ℕ)
    (u : paperSlitCharacterDomain α j) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : paperSlitCharacterDomain α j, ∃ M : ℝ, 0 < M ∧
      ‖v.val - u.val‖ < ε ∧
      (∀ᵐ z ∂volume.restrict disk, ‖valueCLM v.val.1 z‖ ≤ M) ∧
      (∀ᵐ z ∂volume.restrict disk, ‖valueCLM v.val.2 z‖ ≤ M) := by
  have ht (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hc := (diskRadial_tendsto (fun n => (ht n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat u.val.1).prodMk_nhds
    (diskRadial_tendsto (fun n => (ht n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat u.val.2)
  obtain ⟨n, hn⟩ := (Metric.tendsto_nhds.mp hc ε hε).exists
  refine ⟨⟨_, paperSlit_radial_mem α j _ (ht n).le u⟩,
    (Real.sqrt (1 / ((n : ℝ) + 1)))⁻¹,
    inv_pos.mpr (Real.sqrt_pos.mpr (ht n)), ?_,
    diskRadial_bounded (ht n) u.val.1, diskRadial_bounded (ht n) u.val.2⟩
  simpa only [dist_eq_norm] using hn

/-- A common logarithmic cutoff retains the exact phase and character. -/
lemma paperSlit_cutoff_mem (α : ℝ) (j l : ℕ)
    (u : paperSlitCharacterDomain α j) :
    (diskCutoff 3 l u.val.1, diskCutoff 3 l u.val.2) ∈ paperSlitCharacterDomain α j := by
  refine ⟨diskCutoff_mem_slitTraceDomain 3 l _ u.property.1, ?_⟩
  exact ⟨diskCutoff_mem_weakCharacterDomain (by decide : 1 ≤ 3) l _ _
      (paperRotation_puncture_root (by decide)) u.property.2.1,
    diskCutoff_mem_weakCharacterDomain (by decide : 1 ≤ 3) l _ _
      (paperRotation_puncture_root (by decide)) u.property.2.2⟩

/-- Every paper slit phase/character domain admits bounded approximants in the
same domain, with both components vanishing almost everywhere in a common
neighborhood of the punctures. Approximation is in the product H1 norm;
no smoothness of the approximants is asserted. -/
lemma exists_paperSlit_puncture_approx (α : ℝ) (j : ℕ)
    (u : paperSlitCharacterDomain α j) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : paperSlitCharacterDomain α j, ∃ M ρ : ℝ, 0 < M ∧ 0 < ρ ∧
      ‖v.val - u.val‖ < ε ∧
      (∀ᵐ z ∂volume.restrict disk, ‖valueCLM v.val.1 z‖ ≤ M) ∧
      (∀ᵐ z ∂volume.restrict disk, ‖valueCLM v.val.2 z‖ ≤ M) ∧
      (∀ᵐ z ∂volume.restrict disk,
        (∃ p ∈ Surface.punctures 3, ‖z - p‖ ≤ ρ) → valueCLM v.val.1 z = 0) ∧
      (∀ᵐ z ∂volume.restrict disk,
        (∃ p ∈ Surface.punctures 3, ‖z - p‖ ≤ ρ) → valueCLM v.val.2 z = 0) := by
  obtain ⟨w, M, hM, hw, hb1, hb2⟩ := exists_paperSlit_bounded_approx α j u (half_pos hε)
  have ht := slitCutoff_tendsto_of_bounded (by decide : 1 ≤ 3) w.val hb1 hb2
  obtain ⟨l, hl⟩ := (Metric.tendsto_nhds.mp ht (ε / 2) (half_pos hε)).exists
  let v : paperSlitCharacterDomain α j := ⟨_, paperSlit_cutoff_mem α j l w⟩
  refine ⟨v, M, (KsIndex.FaithfulInjection.cutoffEps l) ^ 2, hM,
    pow_pos (KsIndex.FaithfulInjection.cutoffEps_pos l) 2, ?_,
    diskCutoff_value_bound 3 l w.val.1 hb1, diskCutoff_value_bound 3 l w.val.2 hb2,
    diskCutoff_value_vanish_near (by decide : 1 ≤ 3) l w.val.1,
    diskCutoff_value_vanish_near (by decide : 1 ≤ 3) l w.val.2⟩
  have hv : ‖v.val - w.val‖ < ε / 2 := by simpa only [dist_eq_norm] using hl
  calc
    ‖v.val - u.val‖ = ‖(v.val - w.val) + (w.val - u.val)‖ := by congr 1; abel
    _ ≤ ‖v.val - w.val‖ + ‖w.val - u.val‖ := norm_add_le _ _
    _ < ε := by linarith

end KsIndex.Spectral
