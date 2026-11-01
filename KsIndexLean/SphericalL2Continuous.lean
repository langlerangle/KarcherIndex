module

public import KsIndexLean.SphericalL2Realization

@[expose] public section


open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

lemma canonical_L2_mass_eq_norm_sq (f : Lp ℂ 2 (volume : Measure Ambient).toSphere) :
    (∫⁻ p, ENNReal.ofReal (‖f p‖ ^ 2) ∂(volume : Measure Ambient).toSphere) =
      ENNReal.ofReal (‖f‖ ^ 2) := by
  have h := lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := (f : Sphere → ℂ))
    (μ := (volume : Measure Ambient).toSphere) (by norm_num : (0 : ℝ) < 2)
  have he : eLpNorm' (f : Sphere → ℂ) 2 (volume : Measure Ambient).toSphere = ‖f‖ₑ := by
    rw [Lp.enorm_def, eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (Lp.memLp f).aestronglyMeasurable]
    norm_num
  rw [he] at h
  simpa only [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h

lemma sphereChartL2_norm_sq_mass {A : Set Circle₁} (hA : IsOpen A)
    (q : SphereChartSpace A hA) :
    ‖sphereChartL2LinearMap hA q‖ ^ 2 =
      (∫⁻ p, ENNReal.ofReal (‖sphereChartValue hA q p‖ ^ 2)
        ∂(volume : Measure Ambient).toSphere).toReal := by
  have he : (∫⁻ p, ENNReal.ofReal (‖sphereChartL2LinearMap hA q p‖ ^ 2)
      ∂(volume : Measure Ambient).toSphere) =
      ∫⁻ p, ENNReal.ofReal (‖sphereChartValue hA q p‖ ^ 2)
        ∂(volume : Measure Ambient).toSphere := by
    apply lintegral_congr_ae
    filter_upwards [sphereChartToL2_coe_ae hA q] with p hp
    rw [show sphereChartL2LinearMap hA q p = sphereChartValue hA q p from hp]
  rw [canonical_L2_mass_eq_norm_sq] at he
  exact (ENNReal.toReal_ofReal (sq_nonneg _)).symm.trans (congrArg ENNReal.toReal he)

lemma sphereChartL2LinearMap_bound {A : Set Circle₁} (hA : IsOpen A)
    (q : SphereChartSpace A hA) : ‖sphereChartL2LinearMap hA q‖ ≤ 3 * ‖q‖ := by
  have h := (sphereChartH1Squared_norm_comparison hA q).2
  have he := sphereJoinedEnergy_eq (chartDiskPair hA q).val.1 (chartDiskPair hA q).val.2
  have hn : 0 ≤ sphereJoinedEnergy (chartDiskPair hA q).val.1 (chartDiskPair hA q).val.2 := by
    rw [he]
    positivity
  rw [sphereChartH1Squared, sphereJoinedH1Squared] at h
  change _ + _ ≤ _ at h
  have hm := sphereChartL2_norm_sq_mass hA q
  unfold sphereChartValue at hm
  nlinarith [norm_nonneg q, norm_nonneg (sphereChartL2LinearMap hA q)]

/-- The actual canonical L2 realization is bounded for the complete carrier norm. -/
def sphereChartL2CLM {A : Set Circle₁} (hA : IsOpen A) :
    SphereChartSpace A hA →L[ℂ] Lp ℂ 2 (volume : Measure Ambient).toSphere :=
  (sphereChartL2LinearMap hA).mkContinuous 3 (sphereChartL2LinearMap_bound hA)

lemma sphereChartL2CLM_injective {A : Set Circle₁} (hA : IsOpen A) :
    Function.Injective (sphereChartL2CLM hA) := sphereChartL2LinearMap_injective hA

end KsIndex.Spherical
