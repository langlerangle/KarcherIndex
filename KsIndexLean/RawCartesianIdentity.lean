module

public import KsIndexLean.RawThreePairings

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

def rawCartesianOne (ψ : ℂ → ℝ) (u v q : ℂ → ℂ) (r : ℝ) (w : Circle₁) : ℂ :=
  r • (fderiv ℝ ψ (r • (w : ℂ)) 1 • u (r • (w : ℂ))) +
    r • (((w : ℂ).re * ψ (r • (w : ℂ))) • v (r • (w : ℂ))) -
    ((w : ℂ).im * ψ (r • (w : ℂ))) • q (r • (w : ℂ))

def rawCartesianI (ψ : ℂ → ℝ) (u v q : ℂ → ℂ) (r : ℝ) (w : Circle₁) : ℂ :=
  r • (fderiv ℝ ψ (r • (w : ℂ)) Complex.I • u (r • (w : ℂ))) +
    r • (((w : ℂ).im * ψ (r • (w : ℂ))) • v (r • (w : ℂ))) +
    ((w : ℂ).re * ψ (r • (w : ℂ))) • q (r • (w : ℂ))

/-- Cartesian radial-circle identity for explicitly given raw value/radial/angular fields. -/
theorem raw_cartesian_identity_one {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {u v q : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (hv : MemLp v 2 (volume.restrict (annulusSet a b)))
    (hq : MemLp q 2 (volume.restrict (annulusSet a b)))
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b)
      (sliceLp a b u) (sliceLp a b v) 1)
    (hθ : ∀ᵐ r ∂volume.restrict (Ioo a b),
      (sliceLp a b u r, sliceLp a b q r) ∈ circleAngularGraph)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψa : ∀ w : Circle₁, ψ (a • (w : ℂ)) = 0)
    (hψb : ∀ w : Circle₁, ψ (b • (w : ℂ)) = 0) :
    (∫ r in a..b, ∫ w : Circle₁, rawCartesianOne ψ u v q r w ∂circleMeasure) = 0 := by
  have hz := cartesian_profile_identity_one hab hw (intervalIntegrable_sliceLp ha hab hv)
    hθ hψ hψa hψb
  have he := integral_three_slice_pairings ha hab hu hv hq
    (fun r => r • cartesianCircleTest ψ hψ r 1)
    (weightedCircleTest (coordinateCircle Complex.reCLM) ψ hψ)
    (fun r => coordinateCircle Complex.imCLM * scaledCircleTest ψ hψ r) (-1)
  have hzero : (∫ r in a..b, ∫ w : Circle₁,
      star ((r • cartesianCircleTest ψ hψ r 1) w) * sliceFun u r w +
      star (weightedCircleTest (coordinateCircle Complex.reCLM) ψ hψ r w) * sliceFun v r w +
      (-1 : ℝ) • (star ((coordinateCircle Complex.imCLM * scaledCircleTest ψ hψ r) w) *
        sliceFun q r w) ∂circleMeasure) = 0 := by
    rw [← he]
    simpa only [map_smul, smul_apply, neg_one_smul, sub_eq_add_neg] using hz
  simpa [rawCartesianOne, cartesianCircleTest, coordinateCircle, weightedCircleTest,
    scaledCircleTest, realAngularMap, scaledAngularTest, sliceFun,
    Complex.real_smul, mul_assoc, sub_eq_add_neg] using hzero

/-- The complementary raw Cartesian identity has the positive angular contribution. -/
theorem raw_cartesian_identity_I {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {u v q : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (hv : MemLp v 2 (volume.restrict (annulusSet a b)))
    (hq : MemLp q 2 (volume.restrict (annulusSet a b)))
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b)
      (sliceLp a b u) (sliceLp a b v) 1)
    (hθ : ∀ᵐ r ∂volume.restrict (Ioo a b),
      (sliceLp a b u r, sliceLp a b q r) ∈ circleAngularGraph)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψa : ∀ w : Circle₁, ψ (a • (w : ℂ)) = 0)
    (hψb : ∀ w : Circle₁, ψ (b • (w : ℂ)) = 0) :
    (∫ r in a..b, ∫ w : Circle₁, rawCartesianI ψ u v q r w ∂circleMeasure) = 0 := by
  have hz := cartesian_profile_identity_I hab hw (intervalIntegrable_sliceLp ha hab hv)
    hθ hψ hψa hψb
  have he := integral_three_slice_pairings ha hab hu hv hq
    (fun r => r • cartesianCircleTest ψ hψ r Complex.I)
    (weightedCircleTest (coordinateCircle Complex.imCLM) ψ hψ)
    (fun r => coordinateCircle Complex.reCLM * scaledCircleTest ψ hψ r) 1
  have hzero : (∫ r in a..b, ∫ w : Circle₁,
      star ((r • cartesianCircleTest ψ hψ r Complex.I) w) * sliceFun u r w +
      star (weightedCircleTest (coordinateCircle Complex.imCLM) ψ hψ r w) * sliceFun v r w +
      (1 : ℝ) • (star ((coordinateCircle Complex.reCLM * scaledCircleTest ψ hψ r) w) *
        sliceFun q r w) ∂circleMeasure) = 0 := by
    rw [← he]
    simpa only [map_smul, smul_apply, one_smul] using hz
  simpa [rawCartesianI, cartesianCircleTest, coordinateCircle, weightedCircleTest,
    scaledCircleTest, realAngularMap, scaledAngularTest, sliceFun,
    Complex.real_smul, mul_assoc] using hzero

end KsIndex.Trace
