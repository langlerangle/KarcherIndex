module

public import KsIndexLean.PolarTestSeparation

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

/-- A real angular test embedded into complex continuous circle functions. -/
def realAngularMap (H : ℂ → ℝ) (hH : Continuous H) : C(Circle₁, ℂ) :=
  ⟨fun w => (H w : ℂ), Complex.continuous_ofReal.comp (hH.comp continuous_subtype_val)⟩

lemma realAngular_pairing_ae {a b : ℝ} (ha : 0 < a) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (H : ℂ → ℝ) (hH : Continuous H) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      inner ℂ (ContinuousMap.toLp 2 circleMeasure ℂ (realAngularMap H hH)) (sliceLp a b u t) =
        ∫ w : Circle₁, H w • sliceFun u t w ∂circleMeasure := by
  filter_upwards [ae_sliceFun_memLp ha hu, ae_restrict_mem measurableSet_Ioo] with t ht htI
  rw [sliceLp_of_memLp htI ht, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := circleMeasure) (𝕜 := ℂ)
    (realAngularMap H hH), ht.coeFn_toLp] with w hw hw'
  rw [hw, hw']
  simp [realAngularMap, RCLike.inner_apply, mul_comm]

lemma integrableOn_test_smul_slice {a b : ℝ} (ha : 0 < a) (hab : a < b) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    {χ : ℝ → ℝ} (hc : Continuous χ) (hs : HasCompactSupport χ) :
    IntegrableOn (fun t => χ t • sliceLp a b u t) (Ioo a b) volume := by
  have hi : IntegrableOn (sliceLp a b u) (Ioo a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mp (intervalIntegrable_sliceLp ha hab hu)
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
  exact hi.bdd_smul C hc.aestronglyMeasurable.restrict (Filter.Eventually.of_forall hC)

lemma realAngular_pairing_integral {a b : ℝ} (ha : 0 < a) (hab : a < b) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    {χ : ℝ → ℝ} (hc : Continuous χ) (hs : HasCompactSupport χ)
    (H : ℂ → ℝ) (hH : Continuous H) :
    inner ℂ (ContinuousMap.toLp 2 circleMeasure ℂ (realAngularMap H hH))
      (∫ t in Ioo a b, χ t • sliceLp a b u t) =
    ∫ t in Ioo a b, χ t • (∫ w : Circle₁, H w • sliceFun u t w ∂circleMeasure) := by
  rw [← integral_inner (integrableOn_test_smul_slice ha hab hu hc hs)]
  apply integral_congr_ae
  filter_upwards [realAngular_pairing_ae ha hu H hH] with t ht
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (χ t) (sliceLp a b u t)]
  rw [inner_smul_real_right, ht]

/-- Testing the vector difference against every real smooth angular restriction gives zero. -/
lemma realAngular_weak_difference {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo a b) {H : ℂ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume (annulusOpens a b) u U)
    (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (h1 : MemLp (fun z => U z 1) 2 (volume.restrict (annulusSet a b)))
    (hI : MemLp (fun z => U z Complex.I) 2 (volume.restrict (annulusSet a b))) :
    inner ℂ (ContinuousMap.toLp 2 circleMeasure ℂ (realAngularMap H hH.continuous))
      ((∫ t in Ioo a b, deriv χ t • sliceLp a b u t) +
        ∫ t in Ioo a b, χ t • sliceLp a b (radialField U) t) = 0 := by
  rw [inner_add_right, realAngular_pairing_integral ha hab hu
    (contDiff_infty_iff_deriv.mp hχ).2.continuous hχc.deriv H hH.continuous,
    realAngular_pairing_integral ha hab (memLp_radialField ha h1 hI)
      hχ.continuous hχc H hH.continuous,
    radial_pairing_identity ha hab hχ hχc hχs hH hw hu h1 hI, neg_add_cancel]

/-- Real smooth angular tests suffice for complex L² separation. -/
lemma realAngular_tests_separate (d : Lp ℂ 2 circleMeasure)
    (hd : ∀ (H : ℂ → ℝ) (hH : ContDiff ℝ (⊤ : ℕ∞) H),
      inner ℂ (ContinuousMap.toLp 2 circleMeasure ℂ (realAngularMap H hH.continuous)) d = 0) :
    d = 0 := by
  apply smoothCircle_tests_separate d
  intro f hf
  obtain ⟨H, hH, he⟩ := hf
  have hr : ContDiff ℝ (⊤ : ℕ∞) (fun z => (H z).re) := Complex.reCLM.contDiff.comp hH
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun z => (H z).im) := Complex.imCLM.contDiff.comp hH
  have hsplit : f = realAngularMap (fun z => (H z).re) hr.continuous +
      Complex.I • realAngularMap (fun z => (H z).im) hi.continuous := by
    ext w
    rw [← he w]
    simp [realAngularMap, mul_comm Complex.I, Complex.re_add_im]
  rw [hsplit, map_add, map_smul, inner_add_left, inner_smul_left, hd _ hr, hd _ hi]
  simp

/-- The actual L²-valued weak radial test identity on the open interval. -/
theorem radial_vector_identity {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo a b) {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume (annulusOpens a b) u U)
    (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (h1 : MemLp (fun z => U z 1) 2 (volume.restrict (annulusSet a b)))
    (hI : MemLp (fun z => U z Complex.I) 2 (volume.restrict (annulusSet a b))) :
    (∫ t in Ioo a b, deriv χ t • sliceLp a b u t) =
      -∫ t in Ioo a b, χ t • sliceLp a b (radialField U) t := by
  apply eq_neg_of_add_eq_zero_left
  apply realAngular_tests_separate
  intro H hH
  exact realAngular_weak_difference ha hab hχ hχc hχs hH hw hu h1 hI

/-- The L²-valued radial slice has weak derivative given by the radial field. -/
theorem hasWeakLineDerivOn_sliceLp {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume (annulusOpens a b) u U)
    (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (h1 : MemLp (fun z => U z 1) 2 (volume.restrict (annulusSet a b)))
    (hI : MemLp (fun z => U z Complex.I) 2 (volume.restrict (annulusSet a b))) :
    TauCeti.HasWeakLineDerivOn volume (intervalOpens a b)
      (sliceLp a b u) (sliceLp a b (radialField U)) 1 := by
  have hi (v : ℂ → ℂ) (hv : MemLp v 2 (volume.restrict (annulusSet a b))) :
      IntegrableOn (sliceLp a b v) (Ioo a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mp (intervalIntegrable_sliceLp ha hab hv)
  apply (TauCeti.hasWeakLineDerivOn_iff (hi u hu).locallyIntegrableOn
    (hi (radialField U) (memLp_radialField ha h1 hI)).locallyIntegrableOn).mpr
  intro χ hχ hχc hχs
  have hv := radial_vector_identity ha hab hχ hχc hχs hw hu h1 hI
  have hl : (∫ t in Ioo a b, deriv χ t • sliceLp a b u t) =
      ∫ t, deriv χ t • sliceLp a b u t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [deriv_eq_zero_of_notMem_tsupport (fun h => ht (hχs h)), zero_smul]
  have hr : (∫ t in Ioo a b, χ t • sliceLp a b (radialField U) t) =
      ∫ t, χ t • sliceLp a b (radialField U) t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [image_eq_zero_of_notMem_tsupport (fun h => ht (hχs h)), zero_smul]
  rw [hl, hr] at hv
  simpa only [lineDeriv_one_eq_deriv] using hv

/-- Interval integrability of the value and radial-field slices, together with the weak derivative
identity on the open interval; no endpoint values are asserted. -/
theorem weak_polar_pullback {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume (annulusOpens a b) u U)
    (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (h1 : MemLp (fun z => U z 1) 2 (volume.restrict (annulusSet a b)))
    (hI : MemLp (fun z => U z Complex.I) 2 (volume.restrict (annulusSet a b))) :
    IntervalIntegrable (sliceLp a b u) volume a b ∧
    IntervalIntegrable (sliceLp a b (radialField U)) volume a b ∧
    TauCeti.HasWeakLineDerivOn volume (intervalOpens a b)
      (sliceLp a b u) (sliceLp a b (radialField U)) 1 :=
  ⟨intervalIntegrable_sliceLp ha hab hu,
    intervalIntegrable_sliceLp ha hab (memLp_radialField ha h1 hI),
    hasWeakLineDerivOn_sliceLp ha hab hw hu h1 hI⟩

end KsIndex.Trace
