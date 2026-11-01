module

public import KsIndexLean.CartesianCircleMaps

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

/-- The real Cartesian weak identity, still expressed in radial-circle pairings. -/
theorem cartesian_profile_identity_one {a b : ℝ} (hab : a < b)
    {f g h : ℝ → Lp ℂ 2 circleMeasure}
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (hg : IntervalIntegrable g volume a b)
    (hθ : ∀ᵐ r ∂volume.restrict (Ioo a b), (f r, h r) ∈ circleAngularGraph)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (ha : ∀ w : Circle₁, ψ (a • (w : ℂ)) = 0)
    (hb : ∀ w : Circle₁, ψ (b • (w : ℂ)) = 0) :
    (∫ r in a..b,
      r • circleTestFunctionalMap (cartesianCircleTest ψ hψ r 1) (f r) +
      circleTestFunctionalMap (weightedCircleTest (coordinateCircle Complex.reCLM) ψ hψ r)
        (g r) -
      circleTestFunctionalMap (coordinateCircle Complex.imCLM * scaledCircleTest ψ hψ r)
        (h r)) = 0 := by
  trans ∫ r in a..b,
    circleTestFunctionalMap (weightedCircleTest (coordinateCircle Complex.reCLM) ψ hψ r)
      (g r) +
    circleTestFunctionalMap (weightedCircleTestDeriv (coordinateCircle Complex.reCLM) ψ hψ r)
      (f r)
  · apply intervalIntegral.integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hθ, volume.ae_ne b]
      with r hr hrb hrI
    rw [uIoc_of_le hab.le] at hrI
    have hθr := hr ⟨hrI.1, lt_of_le_of_ne hrI.2 hrb⟩
    rw [weightedCircleTestDeriv_re, map_add, map_smul,
      add_apply, smul_apply,
      coordinateAngularTest_pairing hθr Complex.imCLM hψ r]
    abel
  · exact weighted_circle_radial_ibp_zero hab hw hg _ hψ ha hb

/-- The imaginary Cartesian weak identity has the complementary angular sign. -/
theorem cartesian_profile_identity_I {a b : ℝ} (hab : a < b)
    {f g h : ℝ → Lp ℂ 2 circleMeasure}
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (hg : IntervalIntegrable g volume a b)
    (hθ : ∀ᵐ r ∂volume.restrict (Ioo a b), (f r, h r) ∈ circleAngularGraph)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (ha : ∀ w : Circle₁, ψ (a • (w : ℂ)) = 0)
    (hb : ∀ w : Circle₁, ψ (b • (w : ℂ)) = 0) :
    (∫ r in a..b,
      r • circleTestFunctionalMap (cartesianCircleTest ψ hψ r Complex.I) (f r) +
      circleTestFunctionalMap (weightedCircleTest (coordinateCircle Complex.imCLM) ψ hψ r)
        (g r) +
      circleTestFunctionalMap (coordinateCircle Complex.reCLM * scaledCircleTest ψ hψ r)
        (h r)) = 0 := by
  trans ∫ r in a..b,
    circleTestFunctionalMap (weightedCircleTest (coordinateCircle Complex.imCLM) ψ hψ r)
      (g r) +
    circleTestFunctionalMap (weightedCircleTestDeriv (coordinateCircle Complex.imCLM) ψ hψ r)
      (f r)
  · apply intervalIntegral.integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hθ, volume.ae_ne b]
      with r hr hrb hrI
    rw [uIoc_of_le hab.le] at hrI
    have hθr := hr ⟨hrI.1, lt_of_le_of_ne hrI.2 hrb⟩
    rw [weightedCircleTestDeriv_im, map_sub, map_smul,
      sub_apply, smul_apply,
      coordinateAngularTest_pairing hθr Complex.reCLM hψ r]
    abel
  · exact weighted_circle_radial_ibp_zero hab hw hg _ hψ ha hb

end KsIndex.Trace
