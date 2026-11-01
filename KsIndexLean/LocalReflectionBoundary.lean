module

public import KsIndexLean.GeneralReflectionBoundary
public import KsIndexLean.SeamMollificationSupport

@[expose] public section


/-! Pointwise boundary conditions from reflected representatives on open arcs.
The unmatched part of the unit circle is removed from each seam domain. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Surface KsIndex.FormIndex

/-- AE equality to the reflected field forces the same pointwise symmetry
for every continuous representative, including on the circle. -/
theorem continuous_joined_reflection_on {A : Set Circle₁} (hA : IsOpen A) (u : ComplexH1) (c : ℂ) (hc : c * c = 1)
    {F : ℂ → ℂ}
    (hF : ContinuousOn F (seamDomain A hA : Set ℂ))
    (ha : joinedDiskValue u u c =ᵐ[volume.restrict
      (seamDomain A hA : Set ℂ)] F) :
    ∀ z ∈ seamDomain A hA, F (Bracket.σ z) = c * F z := by
  let Ω := seamDomain A hA
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
      have := hz.1
      linarith [this.1])
    rw [← hp (seamDomain_sigma hA hz), ← he hz]
    exact joined_self_reflection u c hc hz0 hn
  have hs : ContinuousOn Bracket.σ (Ω : Set ℂ) := by
    intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (by
      have := hz.1
      linarith [this.1])
    exact (Bracket.contDiffAt_σ hz0).continuousAt.continuousWithinAt
  exact MeasureTheory.Measure.eqOn_of_ae_eq hae (hF.comp hs (fun _ hz => seamDomain_sigma hA hz))
    (continuousOn_const.mul hF) (by rw [Ω.isOpen.interior_eq]; exact subset_closure)

/-- Odd reflection forces the Dirichlet boundary value pointwise. -/
theorem odd_joined_boundary_zero_on {A : Set Circle₁} (hA : IsOpen A) (u : ComplexH1) {F : ℂ → ℂ}
    (hF : ContinuousOn F (seamDomain A hA : Set ℂ))
    (ha : joinedDiskValue u u (-1) =ᵐ[volume.restrict
      (seamDomain A hA : Set ℂ)] F)
    {z : ℂ} (hz : ‖z‖ = 1) (hm : z ∈ seamDomain A hA) : F z = 0 := by
  have h := continuous_joined_reflection_on hA u (-1) (by norm_num) hF ha z hm
  rw [Bracket.σ_self hz, neg_one_mul] at h
  linear_combination (1 / 2 : ℂ) * h

/-- Even reflection forces zero Euclidean radial derivative on the circle.
Conformal rescaling does not change this homogeneous Neumann condition. -/
theorem even_joined_boundary_normal_zero_on {A : Set Circle₁} (hA : IsOpen A) (u : ComplexH1) {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (seamDomain A hA : Set ℂ))
    (ha : joinedDiskValue u u 1 =ᵐ[volume.restrict
      (seamDomain A hA : Set ℂ)] F)
    {z : ℂ} (hz : ‖z‖ = 1) (hm : z ∈ seamDomain A hA) : fderiv ℝ F z z = 0 := by
  have hsym := continuous_joined_reflection_on hA u 1 (by norm_num) hF.continuousOn ha
  have he : (F ∘ Bracket.σ) =ᶠ[nhds z] F := by
    apply Filter.eventuallyEq_of_mem ((seamDomain A hA).isOpen.mem_nhds hm)
    intro w hw
    simpa only [Function.comp_apply, one_mul] using hsym w hw
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hd : DifferentiableAt ℝ F z :=
    (hF.contDiffAt ((seamDomain A hA).isOpen.mem_nhds hm)).differentiableAt
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


end KsIndex.Trace

#print axioms KsIndex.Trace.continuous_joined_reflection_on

#print axioms KsIndex.Trace.odd_joined_boundary_zero_on

#print axioms KsIndex.Trace.even_joined_boundary_normal_zero_on
