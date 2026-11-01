module

public import KsIndexLean.PaperDiskClassical

@[expose] public section


/-! Exact L² and Dirichlet energy of smooth representatives of the adopted
disk carrier. Boundary normalization does not enter these open-disk integrals. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Weq
open KsIndex.WeakH1 KsIndex.Surface

lemma smooth_representative_memLp (u : ComplexH1) {F : ℂ → ℂ}
    (ha : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] F) :
    MemLp F 2 (volume.restrict (WeakH1.disk : Set ℂ)) := MemLp.ae_eq ha (Lp.memLp (valueCLM u))

lemma smooth_representative_mass_integrable (u : ComplexH1) {F : ℂ → ℂ}
    (ha : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] F) :
    IntegrableOn (fun z => ‖F z‖ ^ 2) (WeakH1.disk : Set ℂ) :=
  (memLp_two_iff_integrable_sq_norm (smooth_representative_memLp u ha).aestronglyMeasurable).mp
    (smooth_representative_memLp u ha)

lemma smooth_representative_gradient_ae (u : ComplexH1) {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (WeakH1.disk : Set ℂ))
    (ha : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] F) :
    gradSq F =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)]
      (fun z => ‖dxLp u z‖ ^ 2 + ‖dyLp u z‖ ^ 2) := by
  obtain ⟨hx, hy⟩ := disk_smooth_representative_derivatives u hF ha
  change dxLp u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] _ at hx
  change dyLp u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] _ at hy
  filter_upwards [hx, hy] with z hxz hyz
  simp only [gradSq, hxz, hyz]

lemma smooth_representative_energy_integrable (u : ComplexH1) {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (WeakH1.disk : Set ℂ))
    (ha : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] F) :
    IntegrableOn (gradSq F) (WeakH1.disk : Set ℂ) := by
  have hi (f : L2C) : Integrable (fun z => ‖f z‖ ^ 2)
      (volume.restrict (WeakH1.disk : Set ℂ)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp (Lp.memLp f)
  exact ((hi (dxLp u)).add (hi (dyLp u))).congr
    (smooth_representative_gradient_ae u hF ha).symm

/-- The mass agrees exactly with the square of the carrier's L² norm. -/
lemma smooth_representative_mass_eq (u : ComplexH1) {F : ℂ → ℂ}
    (ha : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] F) :
    (∫ z in (WeakH1.disk : Set ℂ), ‖F z‖ ^ 2) = ‖valueCLM u‖ ^ 2 := by
  rw [lp_norm_sq]
  apply integral_congr_ae
  filter_upwards [ha] with z hz
  rw [hz]

/-- The Dirichlet energy is the sum of the squared L² norms of the two weak derivatives. -/
lemma smooth_representative_energy_eq (u : ComplexH1) {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (WeakH1.disk : Set ℂ))
    (ha : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] F) :
    (∫ z in (WeakH1.disk : Set ℂ), gradSq F z) = ‖dxLp u‖ ^ 2 + ‖dyLp u‖ ^ 2 := by
  have hi (f : L2C) : Integrable (fun z => ‖f z‖ ^ 2)
      (volume.restrict (WeakH1.disk : Set ℂ)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp (Lp.memLp f)
  rw [integral_congr_ae (smooth_representative_gradient_ae u hF ha),
    integral_add (hi (dxLp u)) (hi (dyLp u)), lp_norm_sq, lp_norm_sq]

end KsIndex.Weq
