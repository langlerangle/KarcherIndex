module

public import KsIndexLean.EndpointRepresentative
public import KsIndexLean.AnnularSpine
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

@[expose] public section


/-! Closed-annulus circle profiles and agreement with the weak endpoint.
The weak radial identity and a.e. identification are explicit inputs; this module
neither constructs the weak polar pullback nor uses arbitrary raw profile values at endpoints.
Continuity on the closed annulus suffices, hence includes the smooth case. -/

open Set MeasureTheory

namespace KsIndex.Trace

/-- Clamping the radius keeps every circle in the closed annulus. -/
lemma clamped_circle_mem_annulus (t : ℝ) (w : Circle₁) :
    clampT t • (w : ℂ) ∈ annulus := by
  have hw : ‖(w : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
  rw [mem_annulus, norm_smul, hw, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (le_trans (by norm_num) (clampT_mem t).1)]
  exact clampT_mem t

/-- A continuous cylinder obtained solely from continuity on the closed annulus. -/
noncomputable def closedAnnulusCylinder {u : ℂ → ℂ} (hu : ContinuousOn u annulus) :
    C(ℝ × Circle₁, ℂ) where
  toFun p := u (clampT p.1 • (p.2 : ℂ))
  continuous_toFun := hu.comp_continuous
    ((continuous_clampT.comp continuous_fst).smul
      (continuous_subtype_val.comp continuous_snd))
    (fun p => clamped_circle_mem_annulus p.1 p.2)

/-- The genuine L² circle profile, extended by clamping outside the annulus. -/
noncomputable def closedAnnulusProfile {u : ℂ → ℂ} (hu : ContinuousOn u annulus)
    (t : ℝ) : Lp ℂ 2 circleMeasure :=
  ContinuousMap.toLp 2 circleMeasure ℂ ((closedAnnulusCylinder hu).curry t)

lemma continuous_closedAnnulusProfile {u : ℂ → ℂ} (hu : ContinuousOn u annulus) :
    Continuous (closedAnnulusProfile hu) :=
  (ContinuousMap.toLp 2 circleMeasure ℂ).continuous.comp
    (closedAnnulusCylinder hu).curry.continuous

/-- On the closed interval this class is the ordinary radius-t restriction. -/
lemma closedAnnulusProfile_coe_ae {u : ℂ → ℂ} (hu : ContinuousOn u annulus)
    {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    (closedAnnulusProfile hu t : Circle₁ → ℂ) =ᵐ[circleMeasure]
      (fun w => u (t • (w : ℂ))) := by
  have h := ContinuousMap.coeFn_toLp (p := 2) (μ := circleMeasure) (𝕜 := ℂ)
    ((closedAnnulusCylinder hu).curry t)
  change (closedAnnulusProfile hu t : Circle₁ → ℂ) =ᵐ[circleMeasure]
    (fun w => u (clampT t • (w : ℂ))) at h
  rwa [clampT_eq ht] at h

/-- Pointwise a.e. slice identification supplies the L²-valued a.e. bridge. -/
lemma closedAnnulusProfile_ae_eq_of_slices {u : ℂ → ℂ}
    (hu : ContinuousOn u annulus) {f : ℝ → Lp ℂ 2 circleMeasure}
    (hf : ∀ᵐ t ∂volume.restrict (Ioo (1 / 2 : ℝ) 1),
      (f t : Circle₁ → ℂ) =ᵐ[circleMeasure] (fun w => u (t • (w : ℂ)))) :
    closedAnnulusProfile hu =ᵐ[volume.restrict (Ioo (1 / 2 : ℝ) 1)] f := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hf] with t ht hft
  exact Lp.ext ((closedAnnulusProfile_coe_ae hu ⟨ht.1.le, ht.2.le⟩).trans hft.symm)

/-- Once the weak profile is identified a.e., uniqueness recovers the continuous profile
on the whole closed interval, including both endpoints. -/
theorem representative_eq_closedAnnulusProfile {u : ℂ → ℂ}
    (hu : ContinuousOn u annulus) {f g : ℝ → Lp ℂ 2 circleMeasure}
    (hweak : TauCeti.HasWeakLineDerivOn volume (intervalOpens (1 / 2) 1) f g 1)
    (hg : IntervalIntegrable g volume (1 / 2) 1)
    (hf : closedAnnulusProfile hu =ᵐ[volume.restrict (Ioo (1 / 2) 1)] f)
    {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    representative (by norm_num : (1 / 2 : ℝ) < 1) f g t =
      closedAnnulusProfile hu t :=
  (representative_unique (by norm_num) hweak hg
    (continuous_closedAnnulusProfile hu).continuousOn hf ht).symm

/-- In particular, the weak outer endpoint is ordinary circle restriction a.e.
No value of the raw weak profile at radius one is used. -/
theorem representative_endpoint_coe_ae {u : ℂ → ℂ}
    (hu : ContinuousOn u annulus) {f g : ℝ → Lp ℂ 2 circleMeasure}
    (hweak : TauCeti.HasWeakLineDerivOn volume (intervalOpens (1 / 2) 1) f g 1)
    (hg : IntervalIntegrable g volume (1 / 2) 1)
    (hf : closedAnnulusProfile hu =ᵐ[volume.restrict (Ioo (1 / 2) 1)] f) :
    ((representative (by norm_num : (1 / 2 : ℝ) < 1) f g 1 : Lp ℂ 2 circleMeasure) : Circle₁ → ℂ)
      =ᵐ[circleMeasure] (fun w => u (w : ℂ)) := by
  rw [representative_eq_closedAnnulusProfile hu hweak hg hf (by norm_num)]
  simpa using closedAnnulusProfile_coe_ae hu (t := 1) (by norm_num)

end KsIndex.Trace
