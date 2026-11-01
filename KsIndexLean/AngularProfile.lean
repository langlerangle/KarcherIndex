module

public import KsIndexLean.WeakAngularGenerator
public import KsIndexLean.ArcInversionEnergy

@[expose] public section


open Set MeasureTheory
open scoped Distributions

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- The rotation field is bounded on each bounded annulus, so its applied weak
jet is L² whenever the two Cartesian components are L². -/
lemma memLp_angularField {a b : ℝ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (h1 : MemLp (fun z => U z 1) 2 (volume.restrict (annulusSet a b)))
    (hI : MemLp (fun z => U z Complex.I) 2 (volume.restrict (annulusSet a b))) :
    MemLp (angularField U) 2 (volume.restrict (annulusSet a b)) := by
  have hi : MemLp (fun z => (-z.im) • U z 1) 2
      (volume.restrict (annulusSet a b)) := by
    apply (h1.const_smul (|b| : ℝ)).of_le
      (Complex.continuous_im.neg.aestronglyMeasurable.restrict.smul h1.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
    change ‖(-z.im) • U z 1‖ ≤ ‖(|b| : ℝ) • U z 1‖
    simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (Complex.abs_im_le_norm z).trans (hz.2.le.trans (le_abs_self b))
  have hr : MemLp (fun z => z.re • U z Complex.I) 2
      (volume.restrict (annulusSet a b)) := by
    apply (hI.const_smul (|b| : ℝ)).of_le
      (Complex.continuous_re.aestronglyMeasurable.restrict.smul hI.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
    change ‖z.re • U z Complex.I‖ ≤ ‖(|b| : ℝ) • U z Complex.I‖
    simp only [norm_smul, Real.norm_eq_abs, abs_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (Complex.abs_re_le_norm z).trans (hz.2.le.trans (le_abs_self b))
  exact hi.add hr

/-- Unlike the radial derivative, the angular derivative includes one factor of radius. -/
lemma sliceFun_angularField (U : ℂ → ℂ →L[ℝ] ℂ) (t : ℝ) (w : Circle₁) :
    sliceFun (angularField U) t w = t • U (t • (w : ℂ)) ((w : ℂ) * Complex.I) := by
  rw [sliceFun, angularField_apply, smul_mul_assoc, map_smul]

def diskAngularProfile (u : ComplexH1) : ℝ → Lp ℂ 2 circleMeasure :=
  sliceLp (1 / 2) 1 (angularField (Dxy (dxLp u) (dyLp u)))

lemma diskAngularField_memLp (u : ComplexH1) :
    MemLp (angularField (Dxy (dxLp u) (dyLp u))) 2
      (volume.restrict (annulusSet (1 / 2 : ℝ) 1)) := by
  apply memLp_angularField
  · simpa using collar_memLp (dxLp u)
  · simpa using collar_memLp (dyLp u)

lemma diskAngularProfile_integrable (u : ComplexH1) :
    IntervalIntegrable (diskAngularProfile u) volume (1 / 2) 1 :=
  intervalIntegrable_sliceLp (by norm_num) (by norm_num) (diskAngularField_memLp u)

lemma diskAngularProfile_sq_integrable (u : ComplexH1) :
    IntervalIntegrable (fun t => ‖diskAngularProfile u t‖ ^ 2) volume (1 / 2) 1 :=
  intervalIntegrable_sliceLp_norm_sq (by norm_num) (by norm_num) (diskAngularField_memLp u)

def arcAngularProfile (A : Set Circle₁) (u : ComplexH1) :
    ℝ → Lp ℂ 2 (circleMeasure.restrict A) :=
  fun t => boundaryRestrictCLM A (diskAngularProfile u t)

lemma arcAngularProfile_sq_integrable (A : Set Circle₁) (u : ComplexH1) :
    IntervalIntegrable (fun t => ‖arcAngularProfile A u t‖ ^ 2) volume (1 / 2) 1 :=
  boundaryRestrict_sq_integrable A (diskAngularProfile_integrable u)
    (diskAngularProfile_sq_integrable u)

/-- The disk weak derivative supplies the angular integration-by-parts identity on its collar. -/
theorem disk_weak_angular_generator (u : ComplexH1)
    (φ : 𝓓(annulusOpens (1 / 2) 1, ℝ)) :
    (∫ z, fderiv ℝ (φ : ℂ → ℝ) z (z * Complex.I) • valueCLM u z) =
      -∫ z, φ z • angularField (Dxy (dxLp u) (dyLp u)) z :=
  weak_angular_generator ((carrier_hasJet u).mono collar_subset_disk) φ

end KsIndex.Trace
