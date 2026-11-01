module

public import KsIndexLean.RawPlanarInversion
public import KsIndexLean.CartesianReconstructionFields

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace

/-- Explicit radial derivative candidate after radius inversion. -/
def invertedRadialField (u : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(‖z‖ ^ 2)⁻¹ • u (radialInversion z)

lemma measurable_invertedRadialField {u : ℂ → ℂ} (hu : Measurable u) :
    Measurable (invertedRadialField u) :=
  (measurable_norm.pow_const 2).inv.neg.smul (hu.comp measurable_radialInversion)

lemma memLp_invertedRadialField {u : ℂ → ℂ} (hm : Measurable u)
    (hu : MemLp u 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 1))) :
    MemLp (invertedRadialField u) 2 (volume.restrict (annulusSet (1 : ℝ) 2)) := by
  apply memLp_bdd_real_smul (C := 1)
    ((measurable_norm.pow_const 2).inv.neg.aestronglyMeasurable) _
    (memLp_raw_radialInversion hm hu)
  filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
  change |-(‖z‖ ^ 2)⁻¹| ≤ 1
  simp only [abs_neg, abs_inv, abs_pow, abs_norm]
  apply inv_le_one_of_one_le₀
  nlinarith [hz.1]

lemma sliceFun_invertedRadialField (u : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (w : Circle₁) :
    sliceFun (invertedRadialField u) r w = -(r ^ 2)⁻¹ • sliceFun u r⁻¹ w := by
  have hw : ‖(w : ℂ)‖ = 1 := by simp
  simp only [sliceFun, invertedRadialField, radialInversion_circle hr w,
    norm_smul, Real.norm_eq_abs, abs_of_pos hr, hw, mul_one]

lemma ae_raw_inverted_radial_slice {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 1))) :
    ∀ᵐ r ∂volume.restrict (Ioo (1 : ℝ) 2),
      sliceFun (invertedRadialField u) r =ᵐ[circleMeasure]
        (invertedRadialDeriv (sliceLp (1 / 2) 1 u) r : Lp ℂ 2 circleMeasure) := by
  filter_upwards [ae_property_comp_inv_collar (ae_raw_sliceLp (by norm_num) hu),
    ae_restrict_mem measurableSet_Ioo] with r hr hrI
  filter_upwards [hr, Lp.coeFn_smul (-(r ^ 2)⁻¹) (sliceLp (1 / 2) 1 u r⁻¹)] with w hw hs
  simp only [Pi.smul_apply] at hs
  change _ = ((-(r ^ 2)⁻¹) • sliceLp (1 / 2) 1 u r⁻¹ : Lp ℂ 2 circleMeasure) w
  rw [sliceFun_invertedRadialField u (by linarith [hrI.1]), hs, hw]

end KsIndex.Trace
