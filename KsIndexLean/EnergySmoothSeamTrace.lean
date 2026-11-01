module

public import KsIndexLean.SmoothGermTrace
public import KsIndexLean.EnergySmoothWeakCopy
public import KsIndexLean.Bracket

@[expose] public section


open Set MeasureTheory
open scoped ContDiff

namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.FaithfulInjection

/-- The incident seam, on the actual boundary subtype. -/
def seamBoundary (k m : ℕ) (n : ZMod (2 * m)) : Set Circle₁ :=
  {w | (w : ℂ) ∈ Surface.seamArc k m n}

lemma energySmooth_glue_value_ae {k m : ℕ} (u : EnergySmooth k m) (n : ZMod (2 * m)) :
    (valueCLM (energySmoothCopy u n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
      Surface.glue u.val n := by
  filter_upwards [energySmoothCopy_value_ae u n,
    ae_restrict_mem disk.isOpen.measurableSet] with z hz hzD
  have hn : ‖z‖ < 1 := by simpa [disk, Metric.mem_ball, dist_zero_right] using hzD
  rw [hz, Surface.glue, ite_eq_left hn.le]

lemma energySmooth_reflected_glue_value_ae {k m : ℕ} (u : EnergySmooth k m)
    (n : ZMod (2 * m)) :
    (valueCLM (energySmoothCopy u (n + 1)) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
      Surface.glue u.val n ∘ Bracket.σ := by
  have hz0 := (volume.ae_ne (0 : ℂ)).filter_mono
    (ae_mono (Measure.restrict_le_self (s := (disk : Set ℂ))))
  filter_upwards [energySmoothCopy_value_ae u (n + 1),
    ae_restrict_mem disk.isOpen.measurableSet, hz0] with z hz hzD hz0'
  have hn : ‖z‖ < 1 := by simpa [disk, Metric.mem_ball, dist_zero_right] using hzD
  have hσ : 1 < ‖Bracket.σ z‖ := by
    rw [Bracket.norm_σ]
    exact (one_lt_inv₀ (norm_pos_iff.mpr hz0')).mpr hn
  change valueCLM (energySmoothCopy u (n + 1)) z = Surface.glue u.val n (Bracket.σ z)
  rw [hz, Surface.glue, ite_eq_right (not_le.mpr hσ), ← Bracket.σ_apply, Bracket.σ_σ]

lemma energySmooth_left_seam_trace {k m : ℕ} (u : EnergySmooth k m) (n : ZMod (2 * m)) :
    (diskTraceCLM (energySmoothCopy u n) : Circle₁ → ℂ)
      =ᵐ[circleMeasure.restrict (seamBoundary k m n)] (fun w => u.val n (w : ℂ)) := by
  have h := diskTrace_smooth_germs (energySmoothCopy u n)
    (A := seamBoundary k m n) (fun w hw => u.property.1.2.1 n w hw)
    (energySmooth_glue_value_ae u n)
  filter_upwards [h] with w hw
  simpa [Surface.glue, mem_sphere_zero_iff_norm.mp w.property] using hw

lemma energySmooth_right_seam_trace {k m : ℕ} (u : EnergySmooth k m) (n : ZMod (2 * m)) :
    (diskTraceCLM (energySmoothCopy u (n + 1)) : Circle₁ → ℂ)
      =ᵐ[circleMeasure.restrict (seamBoundary k m n)] (fun w => u.val n (w : ℂ)) := by
  have hf : ∀ w ∈ seamBoundary k m n,
      ContDiffAt ℝ ∞ (Surface.glue u.val n ∘ Bracket.σ) (w : ℂ) := by
    intro w hw
    have he : Bracket.σ (w : ℂ) = w := Bracket.σ_self (mem_sphere_zero_iff_norm.mp w.property)
    have hg : ContDiffAt ℝ ∞ (Surface.glue u.val n) (Bracket.σ w) := by
      rw [he]
      exact u.property.1.2.1 n w hw
    apply hg.comp _ (Bracket.contDiffAt_σ _)
    exact norm_ne_zero_iff.mp (by rw [mem_sphere_zero_iff_norm.mp w.property]; norm_num)
  have h := diskTrace_smooth_germs (energySmoothCopy u (n + 1)) hf
    (energySmooth_reflected_glue_value_ae u n)
  filter_upwards [h] with w hw
  simpa [Function.comp_def, Bracket.σ_self (mem_sphere_zero_iff_norm.mp w.property),
    Surface.glue, mem_sphere_zero_iff_norm.mp w.property] using hw

/-- The genuine weak traces match across every smooth incident seam. -/
theorem energySmooth_seam_trace_eq {k m : ℕ} (u : EnergySmooth k m) (n : ZMod (2 * m)) :
    arcTrace (seamBoundary k m n) (energySmoothCopy u n) =
      arcTrace (seamBoundary k m n) (energySmoothCopy u (n + 1)) := by
  apply Lp.ext
  filter_upwards [boundaryRestrict_coe_ae (seamBoundary k m n)
    (diskTraceCLM (energySmoothCopy u n)), boundaryRestrict_coe_ae (seamBoundary k m n)
    (diskTraceCLM (energySmoothCopy u (n + 1))), energySmooth_left_seam_trace u n,
    energySmooth_right_seam_trace u n] with w h1 h2 hl hr
  change (boundaryRestrict _ (diskTraceCLM (energySmoothCopy u n)) : Circle₁ → ℂ) w =
    (boundaryRestrict _ (diskTraceCLM (energySmoothCopy u (n + 1))) : Circle₁ → ℂ) w
  rw [h1, h2, hl, hr]

end KsIndex.Trace
