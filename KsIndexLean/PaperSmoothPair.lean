module

public import KsIndexLean.PaperBoundaryValues
public import KsIndexLean.PaperSeamClassical

@[expose] public section


/-! Actual normalized, finite-energy smooth pairs produced from the paper
radical. Cyclic extension and its rotation character are separate consumers. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.WeakH1 KsIndex.PaperSlitAdapter

/-- A classical pair in the paper's upper/lower convention, before cyclic extension. -/
structure SmoothSlitPair (c : ℂ) where
  upper : ℂ → ℂ
  lower : ℂ → ℂ
  upper_smooth : ContDiffOn ℝ (⊤ : ℕ∞) upper (WeakH1.disk : Set ℂ)
  lower_smooth : ContDiffOn ℝ (⊤ : ℕ∞) lower (WeakH1.disk : Set ℂ)
  upper_energy : IntegrableOn (Surface.gradSq upper) (WeakH1.disk : Set ℂ)
  lower_energy : IntegrableOn (Surface.gradSq lower) (WeakH1.disk : Set ℂ)
  upper_mass : IntegrableOn (fun z => ‖upper z‖ ^ 2) (WeakH1.disk : Set ℂ)
  lower_mass : IntegrableOn (fun z => ‖lower z‖ ^ 2) (WeakH1.disk : Set ℂ)
  upper_pde : ∀ z ∈ (WeakH1.disk : Set ℂ),
    Surface.laplacian upper z + (Surface.potV 3 z : ℂ) * upper z = 0
  lower_pde : ∀ z ∈ (WeakH1.disk : Set ℂ),
    Surface.laplacian lower z + (Surface.potV 3 z : ℂ) * lower z = 0
  upper_exterior : ∀ z, 1 < ‖z‖ → upper z = 0
  lower_exterior : ∀ z, 1 < ‖z‖ → lower z = 0
  upper_puncture : ∀ z ∈ Surface.punctures 3, upper z = 0
  lower_puncture : ∀ z ∈ Surface.punctures 3, lower z = 0
  seam0_value : ∀ z ∈ Surface.arc 3 0, upper z = c * lower z
  seam1_value : ∀ z ∈ Surface.arc 3 1, upper z = lower z
  seam0_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
    (fun z => if ‖z‖ ≤ 1 then upper z else c * lower (Bracket.σ z))
    (seamDomain (boundaryArc 3 0) (isOpen_boundaryArc 3 0) : Set ℂ)
  seam1_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
    (fun z => if ‖z‖ ≤ 1 then upper z else lower (Bracket.σ z))
    (seamDomain (boundaryArc 3 1) (isOpen_boundaryArc 3 1) : Set ℂ)

/-- The actual weak radical has a normalized smooth finite-energy pair
representative. Every regularity, PDE, energy and boundary input is discharged. -/
theorem pair_radical_smooth_pair {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) (hrad : ∀ w, Bpair u w = 0) :
    ∃ p : SmoothSlitPair (Complex.exp ((2 * Real.pi * α) * Complex.I)),
      valueCLM u.val.1 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] p.upper ∧
      valueCLM u.val.2 =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] p.lower := by
  let c := Complex.exp ((2 * Real.pi * α) * Complex.I)
  obtain ⟨f, g, hf, hg, ha, hb⟩ := pair_radical_smooth_representatives u hrad
  obtain ⟨F0, hF0, hA0⟩ := pair_radical_seam_smooth_representative u hrad
  obtain ⟨F1, hF1, hA1⟩ := pair_radical_seam_one_smooth_representative u hrad
  let b := paperBoundary F0 F1
  let d := paperBoundary (fun z => c⁻¹ * F0 z) F1
  let U := filledDisk f b
  let L := filledDisk g d
  have hU := filledDisk_smooth_interior b hf
  have hL := filledDisk_smooth_interior d hg
  have haU := filledDisk_value_ae u.val.1 b ha
  have haL := filledDisk_value_ae u.val.2 d hb
  have hs0 : ContDiffOn ℝ (⊤ : ℕ∞) (filledJoin c f g b d)
      (seamDomain (boundaryArc 3 0) (isOpen_boundaryArc 3 0) : Set ℂ) := by
    apply filledJoin_smooth_on_seamDomain _ c f g b d F0 hF0
    · exact seam_representative_eq_inner _ u.val.1 u.val.2 c hF0.continuousOn hf.continuousOn hA0 ha
    · exact seam_representative_eq_outer _ u.val.1 u.val.2 c hF0.continuousOn hg.continuousOn hA0 hb
    · intro w hw
      exact paperBoundary_arc0 F0 F1 hw
  have hs1 : ContDiffOn ℝ (⊤ : ℕ∞) (filledJoin 1 f g b d)
      (seamDomain (boundaryArc 3 1) (isOpen_boundaryArc 3 1) : Set ℂ) := by
    apply filledJoin_smooth_on_seamDomain _ 1 f g b d F1 hF1
    · exact seam_representative_eq_inner _ u.val.1 u.val.2 1 hF1.continuousOn hf.continuousOn hA1 ha
    · exact seam_representative_eq_outer _ u.val.1 u.val.2 1 hF1.continuousOn hg.continuousOn hA1 hb
    · intro w hw
      exact paperBoundary_arc1 F0 F1 hw
  refine ⟨{
    upper := U, lower := L
    upper_smooth := hU, lower_smooth := hL
    upper_energy := Weq.smooth_representative_energy_integrable u.val.1 hU haU
    lower_energy := Weq.smooth_representative_energy_integrable u.val.2 hL haL
    upper_mass := Weq.smooth_representative_mass_integrable u.val.1 haU
    lower_mass := Weq.smooth_representative_mass_integrable u.val.2 haL
    upper_pde := ?_, lower_pde := ?_
    upper_exterior := fun z hz => filledDisk_eq_exterior f b hz
    lower_exterior := fun z hz => filledDisk_eq_exterior g d hz
    upper_puncture := fun z hz => filledDisk_paper_puncture f F0 F1 hz
    lower_puncture := fun z hz => filledDisk_paper_puncture g _ F1 hz
    seam0_value := fun z hz => filledDisk_paper_arc0_match c (Complex.exp_ne_zero _) f g F0 F1 hz
    seam1_value := fun z hz => filledDisk_paper_arc1_match c f g F0 F1 hz
    seam0_smooth := hs0, seam1_smooth := ?_ }, haU, haL⟩
  · exact Weq.disk_smooth_representative_classical u.val.1
      (fun φ hs hc ht => (pair_radical_D1_fst u hrad φ hs hc ht).1)
      (fun φ hs hc ht => (pair_radical_D1_fst u hrad φ hs hc ht).2) hU haU
  · exact Weq.disk_smooth_representative_classical u.val.2
      (fun φ hs hc ht => (pair_radical_D1_snd u hrad φ hs hc ht).1)
      (fun φ hs hc ht => (pair_radical_D1_snd u hrad φ hs hc ht).2) hL haL
  · have he : filledJoin 1 f g b d = (fun z => if ‖z‖ ≤ 1 then U z else L (Bracket.σ z)) := by
      funext z
      simp only [filledJoin, one_mul, U, L]
    rw [he] at hs1
    exact hs1

end KsIndex.PaperSlitTransport
