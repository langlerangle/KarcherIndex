module

public import KsIndexLean.CartesianProfileIdentity

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

/-- Continuous circle tests multiply an L² slice integrably on the finite circle measure. -/
lemma integrable_circle_test_mul {v : Circle₁ → ℂ} (hv : MemLp v 2 circleMeasure)
    (H : C(Circle₁, ℂ)) : Integrable (fun w => star (H w) * v w) circleMeasure := by
  apply (hv.integrable (by norm_num)).bdd_mul
    (continuous_star.comp H.continuous).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun w => by simpa using H.norm_coe_le_norm w

/-- On each good raw slice the pairing identity holds for every continuous test. -/
lemma circle_pairing_slice_of_memLp {a b r : ℝ} {u : ℂ → ℂ}
    (hr : r ∈ Ioo a b) (hu : MemLp (sliceFun u r) 2 circleMeasure)
    (H : C(Circle₁, ℂ)) :
    circleTestFunctionalMap H (sliceLp a b u r) =
      ∫ w : Circle₁, star (H w) * sliceFun u r w ∂circleMeasure := by
  rw [circleTestFunctionalMap_apply, sliceLp_of_memLp hr hu, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := circleMeasure) (𝕜 := ℂ) H,
    hu.coeFn_toLp] with w hw hv
  rw [hw, hv, RCLike.inner_apply']
  rfl

/-- A single full-measure radial set supports every continuous test, including varying tests. -/
theorem ae_all_circle_pairings {a b : ℝ} (ha : 0 < a) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    ∀ᵐ r ∂volume.restrict (Ioo a b), ∀ H : C(Circle₁, ℂ),
      circleTestFunctionalMap H (sliceLp a b u r) =
        ∫ w : Circle₁, star (H w) * sliceFun u r w ∂circleMeasure := by
  filter_upwards [ae_sliceFun_memLp ha hu, ae_restrict_mem measurableSet_Ioo] with r hr hrI
  exact circle_pairing_slice_of_memLp hrI hr

lemma real_circle_pairing_slice {a b r : ℝ} {u : ℂ → ℂ}
    (hr : r ∈ Ioo a b) (hu : MemLp (sliceFun u r) 2 circleMeasure)
    (H : ℂ → ℝ) (hH : Continuous H) :
    circleTestFunctionalMap (realAngularMap H hH) (sliceLp a b u r) =
      ∫ w : Circle₁, H w • sliceFun u r w ∂circleMeasure := by
  rw [circle_pairing_slice_of_memLp hr hu]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by simp [realAngularMap, Complex.real_smul]

end KsIndex.Trace
