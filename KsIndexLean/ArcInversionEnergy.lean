module

public import KsIndexLean.InversionEnergy
public import KsIndexLean.ArcInvertedGluing

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma diskProfile_sq_integrable (u : ComplexH1) :
    IntervalIntegrable (fun t => ‖diskProfile u t‖ ^ 2) volume (1 / 2) 1 :=
  intervalIntegrable_sliceLp_norm_sq (by norm_num) (by norm_num) (collar_memLp (valueCLM u))

lemma diskRadialProfile_sq_integrable (u : ComplexH1) :
    IntervalIntegrable (fun t => ‖diskRadialProfile u t‖ ^ 2) volume (1 / 2) 1 := by
  apply intervalIntegrable_sliceLp_norm_sq (by norm_num) (by norm_num)
  apply memLp_radialField (by norm_num : (0 : ℝ) < 1 / 2)
  · simpa using collar_memLp (dxLp u)
  · simpa using collar_memLp (dyLp u)

/-- Restricting the angular L² class to an arc preserves square integrability in radius. -/
lemma boundaryRestrict_sq_integrable (A : Set Circle₁) {f : ℝ → Lp ℂ 2 circleMeasure}
    (hf : IntervalIntegrable f volume (1 / 2) 1)
    (h2 : IntervalIntegrable (fun t => ‖f t‖ ^ 2) volume (1 / 2) 1) :
    IntervalIntegrable (fun t => ‖boundaryRestrictCLM A (f t)‖ ^ 2) volume (1 / 2) 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    at hf h2 ⊢
  apply h2.mono_nonneg
    (((boundaryRestrictCLM A).continuous.comp_aestronglyMeasurable
      hf.aestronglyMeasurable).norm.pow 2)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  exact Filter.Eventually.of_forall (fun t =>
    pow_le_pow_left₀ (norm_nonneg _) (boundaryRestrict_norm_le A (f t)) 2)

lemma arcProfile_sq_integrable (A : Set Circle₁) (u : ComplexH1) :
    IntervalIntegrable (fun t => ‖arcProfile A u t‖ ^ 2) volume (1 / 2) 1 :=
  boundaryRestrict_sq_integrable A (disk_weak_polar u).1 (diskProfile_sq_integrable u)

lemma arcRadialProfile_sq_integrable (A : Set Circle₁) (u : ComplexH1) :
    IntervalIntegrable (fun t => ‖arcRadialProfile A u t‖ ^ 2) volume (1 / 2) 1 :=
  boundaryRestrict_sq_integrable A (disk_weak_polar u).2.1 (diskRadialProfile_sq_integrable u)

lemma arcInvertedProfile_sq_integrable (A : Set Circle₁) (u : ComplexH1) :
    IntervalIntegrable (fun r => ‖arcInvertedProfile A u r‖ ^ 2) volume 1 2 :=
  comp_inv_integrable (arcProfile_sq_integrable A u)

lemma arcInvertedRadial_sq_integrable (A : Set Circle₁) (u : ComplexH1) :
    IntervalIntegrable (fun r => ‖invertedRadialDeriv (arcRadialProfile A u) r‖ ^ 2)
      volume 1 2 :=
  invertedRadialDeriv_sq_integrable (arcRadialProfile_sq_integrable A u)

lemma arcInvertedProfile_energy_le (A : Set Circle₁) (u : ComplexH1) :
    (∫ r in (1 : ℝ)..2, ‖arcInvertedProfile A u r‖ ^ 2) ≤
      4 * ∫ t in (1 / 2 : ℝ)..1, ‖arcProfile A u t‖ ^ 2 :=
  integral_comp_inv_sq_le (arcProfile_sq_integrable A u)

lemma arcInvertedRadial_energy_le (A : Set Circle₁) (u : ComplexH1) :
    (∫ r in (1 : ℝ)..2, ‖invertedRadialDeriv (arcRadialProfile A u) r‖ ^ 2) ≤
      ∫ t in (1 / 2 : ℝ)..1, ‖arcRadialProfile A u t‖ ^ 2 :=
  integral_invertedRadialDeriv_sq_le (arcRadialProfile_sq_integrable A u)

/-- Matching actual traces gives a weak radial derivative and finite squared norms
on the whole joined collar. This is a one-dimensional, angular-L²-valued statement. -/
theorem arcJoined_radial_sobolev (A : Set Circle₁) (u v : ComplexH1)
    (hm : arcTrace A u = arcTrace A v) :
    TauCeti.HasWeakLineDerivOn volume (intervalOpens (1 / 2) 2)
      (joinAt 1 (arcProfile A u) (arcInvertedProfile A v))
      (joinAt 1 (arcRadialProfile A u) (invertedRadialDeriv (arcRadialProfile A v))) 1 ∧
    IntervalIntegrable
      (fun r => ‖joinAt 1 (arcProfile A u) (arcInvertedProfile A v) r‖ ^ 2)
      volume (1 / 2) 2 ∧
    IntervalIntegrable
      (fun r => ‖joinAt 1 (arcRadialProfile A u)
        (invertedRadialDeriv (arcRadialProfile A v)) r‖ ^ 2) volume (1 / 2) 2 := by
  exact ⟨(arcInverted_gluing_iff A u v).mpr hm,
    joinAt_sq_integrable (by norm_num) (by norm_num)
      (arcProfile_sq_integrable A u) (arcInvertedProfile_sq_integrable A v),
    joinAt_sq_integrable (by norm_num) (by norm_num)
      (arcRadialProfile_sq_integrable A u) (arcInvertedRadial_sq_integrable A v)⟩

end KsIndex.Trace
