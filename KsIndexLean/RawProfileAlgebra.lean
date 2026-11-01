module

public import KsIndexLean.RawPlanarJoin
public import KsIndexLean.RawInvertedRadialField

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace

lemma ae_raw_smul_profile {a b : ℝ} (c : ℂ) {u : ℂ → ℂ}
    {F : ℝ → Lp ℂ 2 circleMeasure}
    (h : ∀ᵐ r ∂volume.restrict (Ioo a b), sliceFun u r =ᵐ[circleMeasure] F r) :
    ∀ᵐ r ∂volume.restrict (Ioo a b),
      sliceFun (fun z => c • u z) r =ᵐ[circleMeasure] (c • F r : Lp ℂ 2 circleMeasure) := by
  filter_upwards [h] with r hr
  filter_upwards [hr, Lp.coeFn_smul c (F r)] with w hw hs
  simp only [Pi.smul_apply] at hs
  change c • sliceFun u r w = _
  rw [hs, hw]

lemma ae_raw_add_profile {a b : ℝ} {u v : ℂ → ℂ}
    {F G : ℝ → Lp ℂ 2 circleMeasure}
    (hu : ∀ᵐ r ∂volume.restrict (Ioo a b), sliceFun u r =ᵐ[circleMeasure] F r)
    (hv : ∀ᵐ r ∂volume.restrict (Ioo a b), sliceFun v r =ᵐ[circleMeasure] G r) :
    ∀ᵐ r ∂volume.restrict (Ioo a b),
      sliceFun (fun z => u z + v z) r =ᵐ[circleMeasure] (F r + G r : Lp ℂ 2 circleMeasure) := by
  filter_upwards [hu, hv] with r hr hs
  filter_upwards [hr, hs, Lp.coeFn_add (F r) (G r)] with w hw hv ha
  simp only [Pi.add_apply] at ha
  change sliceFun u r w + sliceFun v r w = _
  rw [ha, hw, hv]

lemma ae_raw_cutoff_profile {a b : ℝ} (ha : 0 < a) {η : ℂ → ℝ} (hη : Continuous η)
    {u : ℂ → ℂ} {F : ℝ → Lp ℂ 2 circleMeasure}
    (h : ∀ᵐ r ∂volume.restrict (Ioo a b), sliceFun u r =ᵐ[circleMeasure] F r) :
    ∀ᵐ r ∂volume.restrict (Ioo a b),
      sliceFun (angularCutoffField η u) r =ᵐ[circleMeasure]
        circleMul (realCircleMap η hη) (F r) := by
  filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with r hr hrI
  filter_upwards [hr, circleMul_coe (realCircleMap η hη) (F r)] with w hw hm
  rw [sliceFun_angularCutoffField η u (ha.trans hrI.1), hm, hw]
  rfl

lemma ae_raw_join_profile {a c b : ℝ} (ha : 0 < a) {u v : ℂ → ℂ}
    {F G : ℝ → Lp ℂ 2 circleMeasure}
    (hu : ∀ᵐ r ∂volume.restrict (Ioo a c), sliceFun u r =ᵐ[circleMeasure] F r)
    (hv : ∀ᵐ r ∂volume.restrict (Ioo c b), sliceFun v r =ᵐ[circleMeasure] G r) :
    ∀ᵐ r ∂volume.restrict (Ioo a b),
      sliceFun (radialJoin c u v) r =ᵐ[circleMeasure]
        (joinAt c F G r : Lp ℂ 2 circleMeasure) := by
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hu,
    (ae_restrict_iff' measurableSet_Ioo).mp hv, volume.ae_ne c] with r hl hr hrc hI
  by_cases hle : r ≤ c
  · filter_upwards [hl ⟨hI.1, lt_of_le_of_ne hle hrc⟩] with w hw
    simpa only [sliceFun_radialJoin c u v (ha.trans hI.1), joinAt, ite_eq_left hle] using hw
  · filter_upwards [hr ⟨lt_of_not_ge hle, hI.2⟩] with w hw
    simpa only [sliceFun_radialJoin c u v (ha.trans hI.1), joinAt, ite_eq_right hle] using hw

lemma ae_sliceLp_of_raw_profile {a b : ℝ} {u : ℂ → ℂ}
    {F : ℝ → Lp ℂ 2 circleMeasure}
    (h : ∀ᵐ r ∂volume.restrict (Ioo a b), sliceFun u r =ᵐ[circleMeasure] F r) :
    sliceLp a b u =ᵐ[volume.restrict (Ioo a b)] F := by
  filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with r hr hI
  exact sliceLp_eq_of_raw_ae hI (F r) hr

end KsIndex.Trace
