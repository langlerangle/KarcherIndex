module

public import KsIndexLean.AngularPairing

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma integrableOn_circle_pairing {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {u : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (H : ℂ → ℝ) (hH : Continuous H) :
    IntegrableOn (fun t => ∫ w : Circle₁, H w • sliceFun u t w ∂circleMeasure)
      (Ioo a b) volume := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mp
    (intervalIntegrable_sliceLp ha hab hu)
  have hp := (innerSL ℂ (ContinuousMap.toLp 2 circleMeasure ℂ
    (realAngularMap H hH))).integrable_comp hi
  exact hp.congr (realAngular_pairing_ae ha hu H hH)

/-- For each fixed smooth angular test, the circle weak identity holds a.e. in radius.
The exceptional set is allowed to depend on H. -/
theorem angular_pairing_ae {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {H : ℂ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume (annulusOpens a b) u U)
    (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (h1 : MemLp (fun z => U z 1) 2 (volume.restrict (annulusSet a b)))
    (hI : MemLp (fun z => U z Complex.I) 2 (volume.restrict (annulusSet a b))) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (∫ w : Circle₁, angularTestDeriv H w • sliceFun u t w ∂circleMeasure) =
        -∫ w : Circle₁, H w • sliceFun (angularField U) t w ∂circleMeasure := by
  let L := fun t => ∫ w : Circle₁, angularTestDeriv H w • sliceFun u t w ∂circleMeasure
  let R := fun t => ∫ w : Circle₁, H w • sliceFun (angularField U) t w ∂circleMeasure
  have hL := integrableOn_circle_pairing ha hab hu _ (contDiff_angularTestDeriv hH).continuous
  have hR := integrableOn_circle_pairing ha hab (memLp_angularField h1 hI) H hH.continuous
  have hz : ∀ᵐ t ∂volume, t ∈ Ioo a b → L t + R t = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hL.add hR).locallyIntegrableOn
    intro χ hχ hc hs
    have he : (∫ t in Ioo a b, χ t • (L t + R t)) = ∫ t, χ t • (L t + R t) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      rw [image_eq_zero_of_notMem_tsupport (fun hm => ht (hs hm)), zero_smul]
    change (∫ t, χ t • (L t + R t)) = 0
    rw [← he]
    obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hχ.continuous
    have hiL := hL.bdd_smul C hχ.continuous.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall hC)
    have hiR := hR.bdd_smul C hχ.continuous.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall hC)
    change Integrable (fun t => χ t • L t) (volume.restrict (Ioo a b)) at hiL
    change Integrable (fun t => χ t • R t) (volume.restrict (Ioo a b)) at hiR
    simp_rw [smul_add]
    rw [integral_add hiL hiR]
    exact add_eq_zero_iff_eq_neg.mpr (angular_pairing_identity ha hab hχ hc hs hH hw hu h1 hI)
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hz] with t ht htI
  exact add_eq_zero_iff_eq_neg.mp (ht htI)

/-- The actual adopted disk supplies the fixed-angular-test a.e. identity. -/
theorem disk_angular_pairing_ae (u : ComplexH1) {H : ℂ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) :
    ∀ᵐ t ∂volume.restrict (Ioo (1 / 2 : ℝ) 1),
      (∫ w : Circle₁, angularTestDeriv H w • sliceFun (valueCLM u) t w ∂circleMeasure) =
        -∫ w : Circle₁, H w •
          sliceFun (angularField (Dxy (dxLp u) (dyLp u))) t w ∂circleMeasure := by
  apply angular_pairing_ae (by norm_num) (by norm_num) hH
    ((carrier_hasJet u).mono collar_subset_disk) (collar_memLp (valueCLM u))
  · simpa using collar_memLp (dxLp u)
  · simpa using collar_memLp (dyLp u)

/-- The same fixed-test identity on the actual L²-valued disk profiles. -/
theorem disk_angular_profile_pairing_ae (u : ComplexH1) {H : ℂ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) :
    ∀ᵐ t ∂volume.restrict (Ioo (1 / 2 : ℝ) 1),
      inner ℂ (ContinuousMap.toLp 2 circleMeasure ℂ
        (realAngularMap (angularTestDeriv H) (contDiff_angularTestDeriv hH).continuous))
        (diskProfile u t) =
      -inner ℂ (ContinuousMap.toLp 2 circleMeasure ℂ (realAngularMap H hH.continuous))
        (diskAngularProfile u t) := by
  filter_upwards [disk_angular_pairing_ae u hH,
    realAngular_pairing_ae (by norm_num : (0 : ℝ) < 1 / 2) (collar_memLp (valueCLM u))
      (angularTestDeriv H) (contDiff_angularTestDeriv hH).continuous,
    realAngular_pairing_ae (by norm_num : (0 : ℝ) < 1 / 2) (diskAngularField_memLp u)
      H hH.continuous] with t ht hl hr
  exact hl.trans (ht.trans (congrArg Neg.neg hr.symm))

end KsIndex.Trace
