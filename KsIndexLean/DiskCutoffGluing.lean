module

public import KsIndexLean.CutoffTraceGluing
public import KsIndexLean.AngularGraphGluing
public import KsIndexLean.ArcInvertedGluing

@[expose] public section


open Set MeasureTheory
open scoped ContDiff

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Actual arc traces suffice for cutoff gluing of a disk and a scalar-multiplied inverted disk. -/
theorem disk_cutoff_radial_gluing {A : Set Circle₁} (hA : MeasurableSet A)
    (η : C(Circle₁, ℝ)) (hη : ∀ w ∉ A, η w = 0)
    (u v : ComplexH1) (c : ℂ) (hm : arcTrace A u = c • arcTrace A v) :
    TauCeti.HasWeakLineDerivOn volume (intervalOpens (1 / 2) 2)
      (joinAt 1 (fun r => circleMul η (diskProfile u r))
        (fun r => circleMul η (c • diskProfile v r⁻¹)))
      (joinAt 1 (fun r => circleMul η (diskRadialProfile u r))
        (fun r => circleMul η (c • invertedRadialDeriv (diskRadialProfile v) r))) 1 := by
  have hv := invertedProfile_weak (disk_weak_polar v).2.2 (disk_weak_polar v).2.1
  have hg := invertedRadialDeriv_integrable (disk_weak_polar v).2.1
  apply cutoff_weak_joinAt_of_arc_match (by norm_num) (by norm_num) hA η hη
    (disk_weak_polar u).2.2 (weak_deriv_const_smul_complex c hv)
    (disk_weak_polar u).2.1 (hg.smul c)
  rw [representative_smul_complex (by norm_num : (1 : ℝ) < 2) c hv hg
    (by norm_num : (1 : ℝ) ∈ Icc 1 2), Pi.smul_apply,
    invertedProfile_endpoint (disk_weak_polar v).2.2 (disk_weak_polar v).2.1,
    boundaryRestrict_smul]
  exact hm

/-- The same cutoff joined disk values have their angular product-rule derivative. -/
theorem disk_cutoff_angular_gluing (u v : ComplexH1) (c : ℂ) {η : ℂ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 2),
      (joinAt 1 (fun t => circleMul (realCircleMap η hη.continuous) (diskProfile u t))
        (fun t => circleMul (realCircleMap η hη.continuous) (c • diskProfile v t⁻¹)) r,
       circleMul (realCircleMap η hη.continuous)
         (joinAt 1 (diskAngularProfile u) (fun t => c • diskAngularProfile v t⁻¹) r) +
       circleMul (realCircleMap (angularTestDeriv η) (contDiff_angularTestDeriv hη).continuous)
         (joinAt 1 (diskProfile u) (fun t => c • diskProfile v t⁻¹) r))
      ∈ circleAngularGraph := by
  filter_upwards [joined_disk_circleAngularGraph_ae u v c] with r hr
  have h := circleAngularGraph_cutoff hr hη
  simpa only [joinAt, apply_ite] using h

end KsIndex.Trace
