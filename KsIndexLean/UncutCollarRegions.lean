module

public import KsIndexLean.LocalUncutGluing

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma annular_reconstruction_of_profiles {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {f g q : ℂ → ℂ} {F G Q : ℝ → Lp ℂ 2 circleMeasure}
    (hf : MemLp f 2 (volume.restrict (annulusSet a b)))
    (hg : MemLp g 2 (volume.restrict (annulusSet a b)))
    (hq : MemLp q 2 (volume.restrict (annulusSet a b)))
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) F G 1)
    (hθ : ∀ᵐ r ∂volume.restrict (Ioo a b), (F r, Q r) ∈ circleAngularGraph)
    (hF : ∀ᵐ r ∂volume.restrict (Ioo a b), sliceFun f r =ᵐ[circleMeasure] F r)
    (hG : ∀ᵐ r ∂volume.restrict (Ioo a b), sliceFun g r =ᵐ[circleMeasure] G r)
    (hQ : ∀ᵐ r ∂volume.restrict (Ioo a b), sliceFun q r =ᵐ[circleMeasure] Q r) :
    TauCeti.HasWeakFDerivOn volume (annulusOpens a b) f (reconstructedJet g q) := by
  have heF := ae_sliceLp_of_raw_profile hF
  have heG := ae_sliceLp_of_raw_profile hG
  have heQ := ae_sliceLp_of_raw_profile hQ
  apply annular_weak_reconstruction ha hab hf hg hq
    ((hw.congr_ae heF.symm).congr_ae_deriv heG.symm)
  filter_upwards [heF, heQ, hθ] with r hr hq hθr
  rwa [hr, hq]

/-- The inner collar uses the first disk's actual weak derivative. -/
theorem uncut_inner_collar_weak (u v : ComplexH1) (c : ℂ) :
    TauCeti.HasWeakFDerivOn volume (annulusOpens (1 / 2) 1)
      (joinedDiskValue u v c) (joinedDiskJet u v c) := by
  have h := annular_weak_reconstruction (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) (collar_memLp (valueCLM u))
    (memLp_diskRadialRaw u) (memLp_diskAngularRaw u)
    (disk_weak_polar u).2.2 (disk_circleAngularGraph_ae u)
  apply (h.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [ae_restrict_mem (measurableSet_annulusSet (a := 1 / 2) (b := 1))] with z hz
    simp only [joinedDiskValue, radialJoin, ite_eq_left hz.2.le]
  · filter_upwards [ae_restrict_mem (measurableSet_annulusSet (a := 1 / 2) (b := 1))] with z hz
    simp only [joinedDiskJet, reconstructedJet, reconstructedX, reconstructedY,
      joinedDiskRadial, joinedDiskAngular, radialJoin, ite_eq_left hz.2.le]

/-- The outer collar uses the actual inverted second disk, including the radial chain factor. -/
theorem uncut_outer_collar_weak (u v : ComplexH1) (c : ℂ) :
    TauCeti.HasWeakFDerivOn volume (annulusOpens 1 2)
      (joinedDiskValue u v c) (joinedDiskJet u v c) := by
  have h := annular_reconstruction_of_profiles (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 2)
    ((memLp_raw_radialInversion (Lp.stronglyMeasurable (valueCLM v)).measurable
      (collar_memLp (valueCLM v))).const_smul c)
    ((memLp_invertedRadialField (measurable_diskRadialRaw v) (memLp_diskRadialRaw v)).const_smul c)
    ((memLp_raw_radialInversion (measurable_diskAngularRaw v)
      (memLp_diskAngularRaw v)).const_smul c)
    (weak_deriv_const_smul_complex c
      (invertedProfile_weak (disk_weak_polar v).2.2 (disk_weak_polar v).2.1))
    (inverted_disk_circleAngularGraph_ae v c)
    (ae_raw_smul_profile c (ae_raw_inverted_slice (collar_memLp (valueCLM v))))
    (ae_raw_smul_profile c (ae_raw_inverted_radial_slice (memLp_diskRadialRaw v)))
    (ae_raw_smul_profile c (ae_raw_inverted_slice (memLp_diskAngularRaw v)))
  apply (h.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [ae_restrict_mem (measurableSet_annulusSet (a := 1) (b := 2))] with z hz
    simp only [Pi.smul_apply, joinedDiskValue, radialJoin, ite_eq_right (not_le.mpr hz.1)]
  · filter_upwards [ae_restrict_mem (measurableSet_annulusSet (a := 1) (b := 2))] with z hz
    simp only [joinedDiskJet, reconstructedJet, reconstructedX, reconstructedY,
      joinedDiskRadial, joinedDiskAngular, radialJoin, Pi.smul_apply,
      ite_eq_right (not_le.mpr hz.1)]

end KsIndex.Trace
