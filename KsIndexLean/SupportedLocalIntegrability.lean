module

public import KsIndexLean.SupportedWeakProduct
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

@[expose] public section


open Set MeasureTheory TopologicalSpace
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace

lemma locallyIntegrable_of_supported {F : Type*} [NormedAddCommGroup F]
    {Ω : Opens ℂ} {K : Set ℂ} (hK : IsClosed K) (hs : K ⊆ (Ω : Set ℂ))
    {f : ℂ → F} (hf : LocallyIntegrableOn f Ω volume)
    (hz : ∀ z ∉ K, f z = 0) : LocallyIntegrable f volume := by
  intro z
  by_cases h : z ∈ Ω
  · simpa only [Ω.isOpen.nhdsWithin_eq h] using hf z h
  · have hk : z ∈ Kᶜ := fun hh => h (hs hh)
    refine ⟨Kᶜ, hK.isOpen_compl.mem_nhds hk, ?_⟩
    apply (integrable_zero ℂ F (volume.restrict Kᶜ)).congr
    filter_upwards [ae_restrict_mem hK.measurableSet.compl] with w hw
    exact (hz w hw).symm

/-- Supported smooth multiplication yields a whole-space weak derivative with no
additional integrability assumptions on the product. -/
theorem weakF_smooth_mul_whole {Ω : Opens ℂ} {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hs : tsupport χ ⊆ (Ω : Set ℂ))
    {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume Ω u U) :
    TauCeti.HasWeakFDerivOn volume ⊤ (fun z => χ z • u z)
      (fun z => χ z • U z + (fderiv ℝ χ z).smulRight (u z)) := by
  have hp := weakF_smooth_mul hχ.contDiffOn hw
  apply weakF_smooth_mul_supported le_top hχ.contDiffOn (fun _ h => hs h.2) hw
  · apply LocallyIntegrable.locallyIntegrableOn
    apply locallyIntegrable_of_supported (isClosed_tsupport χ) hs hp.locallyIntegrableOn
    intro z hz
    simp [image_eq_zero_of_notMem_tsupport hz]
  · intro d
    apply LocallyIntegrable.locallyIntegrableOn
    apply locallyIntegrable_of_supported (isClosed_tsupport χ) hs
      (hp.hasWeakLineDerivOn d).locallyIntegrableOn_deriv
    intro z hz
    simp [image_eq_zero_of_notMem_tsupport hz, fderiv_of_notMem_tsupport ℝ hz]

lemma continuous_compact_norm_bound {F : Type*} [NormedAddCommGroup F]
    {f : ℂ → F} (hf : Continuous f) (hs : HasCompactSupport f) :
    ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max 0 C, fun z => ?_⟩
  by_cases hz : z ∈ tsupport f
  · exact (hC z hz).trans (le_max_right _ _)
  · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
    exact le_max_left _ _

lemma memLp_of_zero_outside {F : Type*} [NormedAddCommGroup F]
    {Ω : Set ℂ} (hΩ : MeasurableSet Ω) {f : ℂ → F}
    (hf : MemLp f 2 (volume.restrict Ω)) (hz : ∀ z ∉ Ω, f z = 0) : MemLp f 2 volume := by
  have hi := (memLp_indicator_iff_restrict hΩ).mpr hf
  have he : Ω.indicator f = f := by
    funext z
    by_cases h : z ∈ Ω
    · simp [h]
    · simp [h, hz z h]
  rwa [he] at hi

lemma memLp_continuous_mul_supported {Ω : Opens ℂ} {χ : ℂ → ℝ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ (Ω : Set ℂ))
    {u : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ))) :
    MemLp (fun z => χ z • u z) 2 volume := by
  obtain ⟨C, hC⟩ := continuous_compact_norm_bound hχ hc
  apply memLp_of_zero_outside Ω.isOpen.measurableSet
  · apply hu.of_le_mul (c := C) (hχ.aestronglyMeasurable.smul hu.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun z => by
      change ‖χ z • u z‖ ≤ C * ‖u z‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _)
  · intro z hz
    have hn : z ∉ tsupport χ := fun h => hz (hs h)
    simp [image_eq_zero_of_notMem_tsupport hn]

end KsIndex.Trace
