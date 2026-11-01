module

public import KsIndexLean.SmoothGermTrace
public import KsIndexLean.Bracket

@[expose] public section


open Set MeasureTheory
open scoped ContDiff

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- The first function inside, the phase times the inverted second function outside. -/
def phaseGerm (c : ℂ) (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  if ‖z‖ ≤ 1 then f z else c * g (KsIndex.Bracket.σ z)

/-- A smooth gluing germ proves the actual phase relation between weak traces. -/
theorem arcTrace_phaseGerm {A : Set Circle₁} (u v : ComplexH1) {f g : ℂ → ℂ} (c : ℂ)
    (hu : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f)
    (hv : (valueCLM v : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] g)
    (hgerm : ∀ w ∈ A, ContDiffAt ℝ ∞ (phaseGerm c f g) (w : ℂ)) :
    arcTrace A u = c • arcTrace A v := by
  have hleft : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] phaseGerm c f g := by
    filter_upwards [hu, ae_restrict_mem disk.isOpen.measurableSet] with z hz hzD
    rw [hz, phaseGerm, ite_eq_left (KsIndex.SurfaceForm.mem_disk_iff.mp hzD).le]
  have hright : (valueCLM (c • v) : ℂ → ℂ)
      =ᵐ[volume.restrict (disk : Set ℂ)] phaseGerm c f g ∘ KsIndex.Bracket.σ := by
    have hz0 := (volume.ae_ne (0 : ℂ)).filter_mono
      (ae_mono (Measure.restrict_le_self (s := (disk : Set ℂ))))
    rw [map_smul]
    filter_upwards [hv, Lp.coeFn_smul c (valueCLM v),
      ae_restrict_mem disk.isOpen.measurableSet, hz0] with z hz hc hzD hz0'
    have hn : 1 < ‖KsIndex.Bracket.σ z‖ := by
      rw [KsIndex.Bracket.norm_σ]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hz0')).mpr
        (KsIndex.SurfaceForm.mem_disk_iff.mp hzD)
    simp only [hc, Pi.smul_apply, smul_eq_mul, hz, Function.comp_def, phaseGerm,
      ite_eq_right (not_le.mpr hn), KsIndex.Bracket.σ_σ]
  have hcompose : ∀ w ∈ A,
      ContDiffAt ℝ ∞ (phaseGerm c f g ∘ KsIndex.Bracket.σ) (w : ℂ) := by
    intro w hw
    have he := KsIndex.Bracket.σ_self (mem_sphere_zero_iff_norm.mp w.property)
    have hh : ContDiffAt ℝ ∞ (phaseGerm c f g) (KsIndex.Bracket.σ w) := by
      rw [he]
      exact hgerm w hw
    apply hh.comp _ (KsIndex.Bracket.contDiffAt_σ _)
    exact norm_ne_zero_iff.mp (by rw [mem_sphere_zero_iff_norm.mp w.property]; norm_num)
  have hl := diskTrace_smooth_germs u hgerm hleft
  have hr := diskTrace_smooth_germs (c • v) hcompose hright
  rw [← map_smul]
  apply Lp.ext
  filter_upwards [boundaryRestrict_coe_ae A (diskTraceCLM u),
    boundaryRestrict_coe_ae A (diskTraceCLM (c • v)), hl, hr] with w h1 h2 h3 h4
  change (boundaryRestrict A (diskTraceCLM u) : Circle₁ → ℂ) w =
    (boundaryRestrict A (diskTraceCLM (c • v)) : Circle₁ → ℂ) w
  rw [h1, h2, h3, h4]
  simp only [Function.comp_def, KsIndex.Bracket.σ_self (mem_sphere_zero_iff_norm.mp w.property)]

end KsIndex.Trace
