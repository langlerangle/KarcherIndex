module

public import KsIndexLean.AngularFourierIdentity
public import KsIndexLean.InteriorDiskModes

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma fourierTestLp_inner_unscaled (n : ℤ) (f : Lp ℂ 2 circleMeasure) :
    inner ℂ (fourierTestLp n) f = ((2 * Real.pi : ℝ) : ℂ) * circleFourierCoeff f n := by
  have h := congrArg (fun z : ℂ => ((2 * Real.pi : ℝ) : ℂ) * z) (fourierTestLp_inner n f)
  have hp : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  simpa only [Complex.real_smul, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hp, one_mul] using h

/-- The weak form is conjugate-linear in its first argument, so testing against
e_n extracts the conjugate coefficient. Geometric circle measure contributes 2pi. -/
lemma integral_conj_mul_fourierAmbient (n : ℤ) (f : Lp ℂ 2 circleMeasure) :
    (∫ w : Circle₁, (starRingEnd ℂ) (f w) * fourierAmbient n w ∂circleMeasure) =
      ((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (circleFourierCoeff f n) := by
  have he : (∫ w : Circle₁, (starRingEnd ℂ) (f w) * fourierAmbient n w ∂circleMeasure) =
      inner ℂ f (fourierTestLp n) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [fourierTestLp_coe n] with w hw
    simp only [RCLike.inner_apply, hw]
    ring
  rw [he, ← inner_conj_symm, fourierTestLp_inner_unscaled, map_mul, Complex.conj_ofReal]

lemma slice_conj_fourier_pairing_ae {a b : ℝ} (ha : 0 < a) {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict (annulusSet a b))) (n : ℤ) :
    ∀ᵐ r ∂volume.restrict (Ioo a b),
      (∫ w : Circle₁, (starRingEnd ℂ) (sliceFun f r w) * fourierAmbient n w ∂circleMeasure) =
        ((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (circleFourierCoeff (sliceLp a b f r) n) := by
  filter_upwards [sliceLp_coe_ae ha hf] with r hr
  rw [← integral_conj_mul_fourierAmbient]
  apply integral_congr_ae
  filter_upwards [hr] with w hw
  rw [hw]

lemma interiorDiskMode_pairing_ae {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (u : ComplexH1) (n : ℤ) :
    ∀ᵐ r ∂volume.restrict (Ioo a b),
      (∫ w : Circle₁, (starRingEnd ℂ) (sliceFun (valueCLM u) r w) *
        fourierAmbient n w ∂circleMeasure) =
        ((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskMode hab u n r) := by
  filter_upwards [slice_conj_fourier_pairing_ae ha (interiorAnnulus_memLp hb (valueCLM u)) n,
    interiorDiskRepresentative_ae ha hab hb u] with r hr he
  rw [hr]
  change _ = ((2 * Real.pi : ℝ) : ℂ) *
    (starRingEnd ℂ) (circleCoefficientCLM n (interiorDiskRepresentative hab u r))
  rw [circleCoefficientCLM_apply, ← he]
  rfl

lemma interiorDiskRadialMode_pairing_ae {a b : ℝ} (ha : 0 < a) (hb : b ≤ 1)
    (u : ComplexH1) (n : ℤ) :
    ∀ᵐ r ∂volume.restrict (Ioo a b),
      (∫ w : Circle₁, (starRingEnd ℂ)
        (sliceFun (radialField (Dxy (dxLp u) (dyLp u))) r w) *
        fourierAmbient n w ∂circleMeasure) =
        ((2 * Real.pi : ℝ) : ℂ) * (starRingEnd ℂ) (interiorDiskRadialMode a b u n r) := by
  have hm : MemLp (radialField (Dxy (dxLp u) (dyLp u))) 2
      (volume.restrict (annulusSet a b)) := by
    apply memLp_radialField ha
    · simpa using interiorAnnulus_memLp hb (dxLp u)
    · simpa using interiorAnnulus_memLp hb (dyLp u)
  filter_upwards [slice_conj_fourier_pairing_ae ha hm n] with r hr
  simpa only [interiorDiskRadialMode, interiorDiskRadialProfile, circleCoefficientCLM_apply] using hr

end KsIndex.Trace
