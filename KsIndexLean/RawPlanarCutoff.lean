module

public import KsIndexLean.PolarReconstructionEnergy
public import KsIndexLean.CartesianReconstructionFields

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace

lemma measurable_nUnit : Measurable nUnit := measurable_norm.inv.smul measurable_id

def angularCutoffField (η : ℂ → ℝ) (u : ℂ → ℂ) (z : ℂ) : ℂ := η (nUnit z) • u z

lemma measurable_angularCutoffField {η : ℂ → ℝ} {u : ℂ → ℂ}
    (hη : Measurable η) (hu : Measurable u) : Measurable (angularCutoffField η u) :=
  (hη.comp measurable_nUnit).smul hu

lemma memLp_angularCutoffField {a b : ℝ} (ha : 0 < a)
    {η : ℂ → ℝ} (hη : Continuous η) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    MemLp (angularCutoffField η u) 2 (volume.restrict (annulusSet a b)) := by
  apply memLp_bdd_real_smul (C := ‖realCircleMap η hη‖)
    ((hη.measurable.comp measurable_nUnit).aestronglyMeasurable) _ hu
  filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
  have hn : z ≠ 0 := by intro h; subst z; simpa using (ha.trans hz.1)
  have hw : nUnit z ∈ Circle₁ := by simpa using norm_nUnit hn
  exact (realCircleMap η hη).norm_coe_le_norm ⟨nUnit z, hw⟩

lemma sliceFun_angularCutoffField (η : ℂ → ℝ) (u : ℂ → ℂ)
    {r : ℝ} (hr : 0 < r) (w : Circle₁) :
    sliceFun (angularCutoffField η u) r w = η w • sliceFun u r w := by
  simp only [sliceFun, angularCutoffField, nUnit_of_circle r hr w]

lemma ae_raw_cutoff_slice {a b : ℝ} (ha : 0 < a) {η : ℂ → ℝ} (hη : Continuous η)
    {u : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    ∀ᵐ r ∂volume.restrict (Ioo a b),
      sliceFun (angularCutoffField η u) r =ᵐ[circleMeasure]
        circleMul (realCircleMap η hη) (sliceLp a b u r) := by
  filter_upwards [ae_raw_sliceLp ha hu, ae_restrict_mem measurableSet_Ioo] with r hr hrI
  filter_upwards [hr, circleMul_coe (realCircleMap η hη) (sliceLp a b u r)] with w hw hm
  rw [sliceFun_angularCutoffField η u (ha.trans hrI.1), hm, hw]
  rfl

end KsIndex.Trace
