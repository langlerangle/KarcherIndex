module

public import KsIndexLean.RawSlicePairing

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

lemma three_slice_pairings {a b r : ℝ} {u v q : ℂ → ℂ}
    (hr : r ∈ Ioo a b) (hu : MemLp (sliceFun u r) 2 circleMeasure)
    (hv : MemLp (sliceFun v r) 2 circleMeasure) (hq : MemLp (sliceFun q r) 2 circleMeasure)
    (A B C : C(Circle₁, ℂ)) (s : ℝ) :
    circleTestFunctionalMap A (sliceLp a b u r) +
        circleTestFunctionalMap B (sliceLp a b v r) +
        s • circleTestFunctionalMap C (sliceLp a b q r) =
      ∫ w : Circle₁, star (A w) * sliceFun u r w + star (B w) * sliceFun v r w +
        s • (star (C w) * sliceFun q r w) ∂circleMeasure := by
  have hab := (integrable_circle_test_mul hu A).add (integrable_circle_test_mul hv B)
  change Integrable (fun w => star (A w) * sliceFun u r w +
    star (B w) * sliceFun v r w) circleMeasure at hab
  have hc := (integrable_circle_test_mul hq C).smul s
  change Integrable (fun w => s • (star (C w) * sliceFun q r w)) circleMeasure at hc
  rw [circle_pairing_slice_of_memLp hr hu, circle_pairing_slice_of_memLp hr hv,
    circle_pairing_slice_of_memLp hr hq, integral_add hab hc,
    integral_add (integrable_circle_test_mul hu A) (integrable_circle_test_mul hv B),
    integral_smul]

/-- Three varying continuous tests transfer to a single raw circle integral, with justified sums. -/
theorem integral_three_slice_pairings {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {u v q : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (hv : MemLp v 2 (volume.restrict (annulusSet a b)))
    (hq : MemLp q 2 (volume.restrict (annulusSet a b)))
    (A B C : ℝ → C(Circle₁, ℂ)) (s : ℝ) :
    (∫ r in a..b, circleTestFunctionalMap (A r) (sliceLp a b u r) +
        circleTestFunctionalMap (B r) (sliceLp a b v r) +
        s • circleTestFunctionalMap (C r) (sliceLp a b q r)) =
      ∫ r in a..b, ∫ w : Circle₁,
        star (A r w) * sliceFun u r w + star (B r w) * sliceFun v r w +
        s • (star (C r w) * sliceFun q r w) ∂circleMeasure := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp (ae_sliceFun_memLp ha hu),
    (ae_restrict_iff' measurableSet_Ioo).mp (ae_sliceFun_memLp ha hv),
    (ae_restrict_iff' measurableSet_Ioo).mp (ae_sliceFun_memLp ha hq), volume.ae_ne b]
    with r hur hvr hqr hrb hrI
  rw [uIoc_of_le hab.le] at hrI
  have hr : r ∈ Ioo a b := ⟨hrI.1, lt_of_le_of_ne hrI.2 hrb⟩
  exact three_slice_pairings hr (hur hr) (hvr hr) (hqr hr) (A r) (B r) (C r) s

end KsIndex.Trace
