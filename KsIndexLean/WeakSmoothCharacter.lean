module

public import KsIndexLean.PaperSlitInteriorSmooth
public import KsIndexLean.NaturalCoreCharacter

@[expose] public section


/-! The weak rotation character becomes an exact pointwise character on a
continuous disk representative. No assertion is made outside the open disk. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- The converse representative direction to `weakCharacter_of_value_eq`:
continuity upgrades the genuine weak character to pointwise covariance. -/
theorem continuous_representative_character (u : ComplexH1) {f : ℂ → ℂ}
    (θ : ℝ) (c : ℂ) (hc : u ∈ weakCharacterDomain θ c)
    (hf : ContinuousOn f (disk : Set ℂ))
    (ha : valueCLM u =ᵐ[volume.restrict (disk : Set ℂ)] f) :
    ∀ z ∈ (disk : Set ℂ), f (planeRotation θ z) = c * f z := by
  have hr := (mem_weakCharacterDomain θ c u).mp hc
  have hv : valueCLM (diskRotation θ u) = c • valueCLM u := by
    rw [hr, map_smul]
  have hrot := (measurePreserving_planeRotation_disk θ).quasiMeasurePreserving.ae_eq_comp ha
  have he : (fun z => f (planeRotation θ z)) =ᵐ[volume.restrict (disk : Set ℂ)]
      (fun z => c * f z) := by
    filter_upwards [diskRotation_value_ae θ u, hrot, ha, Lp.coeFn_smul c (valueCLM u)]
      with z hR hC hA hS
    rw [hv, hS] at hR
    change c * valueCLM u z = valueCLM u (planeRotation θ z) at hR
    change valueCLM u (planeRotation θ z) = f (planeRotation θ z) at hC
    rw [hA, hC] at hR
    exact hR.symm
  have hm : MapsTo (planeRotation θ) (disk : Set ℂ) (disk : Set ℂ) := by
    intro z hz
    change dist (planeRotation θ z) 0 < 1
    rw [dist_zero_right, (planeRotation θ).norm_map]
    change dist z 0 < 1 at hz
    simpa only [dist_zero_right] using hz
  exact Measure.eqOn_open_of_ae_eq he disk.isOpen
    (hf.comp (planeRotation θ).continuous.continuousOn hm) (continuousOn_const.mul hf)

end KsIndex.Trace

namespace KsIndex.PaperSlitTransport
open KsIndex.Trace KsIndex.WeakH1

/-- Both disk representatives retain the paper's exact rotation convention. -/
theorem pair_smooth_representatives_character {α : ℝ} {j : ℕ}
    (u : paperSlitCharacterDomain α j) {f g : ℂ → ℂ}
    (hf : ContinuousOn f (disk : Set ℂ)) (hg : ContinuousOn g (disk : Set ℂ))
    (ha : valueCLM u.val.1 =ᵐ[volume.restrict (disk : Set ℂ)] f)
    (hb : valueCLM u.val.2 =ᵐ[volume.restrict (disk : Set ℂ)] g) :
    (∀ z ∈ (disk : Set ℂ), f (planeRotation (-(2 * Real.pi) / 3) z) =
      (KsIndex.FormIndex.zeta 3 ^ j) * f z) ∧
    (∀ z ∈ (disk : Set ℂ), g (planeRotation (-(2 * Real.pi) / 3) z) =
      (KsIndex.FormIndex.zeta 3 ^ j) * g z) := by
  exact ⟨continuous_representative_character u.val.1 _ _ u.property.2.1 hf ha,
    continuous_representative_character u.val.2 _ _ u.property.2.2 hg hb⟩

end KsIndex.PaperSlitTransport
